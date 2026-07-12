#!/usr/bin/env python3
"""Validate the frozen Goal 1 cohort and the Goal 2 registry overlays.

The validator is intentionally standard-library-only and read-only.  With
``--self-check`` it verifies all maintained inputs that exist before the final
classification registry is written.  Normal mode additionally requires and
validates ``docs/Goal2ClassificationRegistry.json``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable

import generate_goal2_registry_checks as lean_checks


REPO_ROOT = Path(__file__).resolve().parents[1]
COHORT_PATH = Path("docs/Goal1ComparisonCohort.json")
COHORT_SIDECAR = Path("docs/Goal1ComparisonCohort.sha256")
MANIFEST_PATH = Path("docs/Goal2SemanticAPIManifest.json")
REGISTRY_PATH = Path("docs/Goal2ClassificationRegistry.json")
SCHEMA_PATH = Path("docs/Goal2ClassificationRegistry.schema.json")
PUBLIC_ROOT_PATH = Path("QuaternionicComputing.lean")
AXIOM_AUDIT_PATH = Path("QuaternionicComputing/AxiomAudit.lean")
CLASSIFICATION_DOC_PATH = Path("docs/EquivalenceClassification.md")

REGISTRY_TABLE_START = "<!-- GOAL2-REGISTRY-TABLE:START -->"
REGISTRY_TABLE_END = "<!-- GOAL2-REGISTRY-TABLE:END -->"

FROZEN_SHA256 = "65efcf04b626ab77b08d4019fd8148750fd8e858f5cfe6263db4faddaa18ef3b"
STAGE10_MANIFEST_COUNT = 1269
STAGE9C_MANIFEST_COUNT = 1100
STAGE9C_STRUCTURAL_SHA256 = (
    "d98dc2ee741dd792c204e088c396c7cbf95b1cc02f98fadceeccf94938da0870"
)
STAGE10_STRUCTURAL_SHA256 = (
    "c9c5e6845f8f2087a690859aad3c9cce4e752f4167d40ce742d246efb0e88229"
)
DIRECT_LABEL = "direct #print axioms target in QuaternionicComputing/AxiomAudit.lean"

AXES = (
    "space",
    "subject",
    "inputScope",
    "observationScope",
    "phase",
    "exactness",
    "ancillaPolicy",
)
ORIGINS = {"goal1Public", "goal1Boundary", "sourceOnly"}
FINAL_STATUSES = {
    "proved",
    "correctedAndProved",
    "partiallyFormalized",
    "intentionallyExcluded",
    "unresolved",
}
SEMANTIC_CLASSES = {
    "sameSpaceBehavior",
    "crossModelSemantics",
    "representativeOrRay",
    "algebraicComparison",
    "structuralSupport",
    "resourceClaim",
    "diagnosticCounterexample",
    "approximationBoundary",
    "sourceOnlyClaim",
}
EVIDENCE_MODES = {
    "proofBearingRelation",
    "proofBearingEquality",
    "proofBearingCertificate",
    "counterexample",
    "nonbehavioralDisposition",
    "resourceDisposition",
    "supportDisposition",
    "sourceOnlyObstruction",
}
DECLARATION_EVIDENCE_MODES = EVIDENCE_MODES - {"sourceOnlyObstruction"}
AUDIT_MODES = {"directRoot", "localEndpoint", "transitive", "notApplicable"}
PROOF_MODES = {
    "proofBearingRelation",
    "proofBearingEquality",
    "proofBearingCertificate",
    "counterexample",
}
NONBEHAVIORAL_MODES = {
    "nonbehavioralDisposition",
    "resourceDisposition",
    "supportDisposition",
}
LEAN_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$")

REGISTRY_TOP_KEYS = {
    "schemaVersion",
    "registryKind",
    "inputs",
    "classificationAxes",
    "families",
    "declarations",
}
FAMILY_KEYS = {
    "id",
    "slug",
    "origin",
    "declarationCount",
    "classification",
    "finalStatus",
    "semanticClass",
    "evidenceMode",
    "strongestRelations",
    "proofDeclarations",
    "consumer",
    "audit",
    "weakerTheorems",
    "strictnessWitnesses",
    "finalDisposition",
    "goal3Boundary",
    "obstruction",
}
DECLARATION_KEYS = {
    "declaration",
    "familyId",
    "classification",
    "semanticClass",
    "evidenceMode",
    "strongestRelations",
    "proofDeclarations",
    "consumer",
    "audit",
    "weakerTheorems",
    "strictnessWitnesses",
    "finalDisposition",
    "goal3Boundary",
}

EMPTY_FAMILY_IDS = tuple(f"EQC-{index:03d}" for index in range(42, 52))
STAGE10_SOURCE_FILES = (
    Path("QuaternionicComputing/Semantics/Approximation/Operator.lean"),
    Path("QuaternionicComputing/Semantics/Approximation/OperatorPhase.lean"),
    Path("QuaternionicComputing/Semantics/Approximation/Quaternion.lean"),
    Path("QuaternionicComputing/Semantics/Approximation/State.lean"),
    Path("QuaternionicComputing/Semantics/Approximation/Distribution.lean"),
    Path("QuaternionicComputing/Semantics/Approximation/Strictness.lean"),
)


class ValidationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def resolve(root: Path, path: Path) -> Path:
    return path if path.is_absolute() else root / path


def load_json(path: Path) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as handle:
            value = json.load(handle)
    except FileNotFoundError as exc:
        raise ValidationError(f"required JSON file is absent: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ValidationError(f"invalid JSON in {path}: {exc}") from exc
    require(isinstance(value, dict), f"expected a JSON object in {path}")
    return value


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def structural_hash(items: list[Any]) -> str:
    payload = json.dumps(
        items, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def nonempty_string(value: Any, label: str) -> str:
    require(isinstance(value, str) and bool(value), f"{label} must be nonempty")
    return value


def lean_name(value: Any, label: str) -> str:
    result = nonempty_string(value, label)
    require(bool(LEAN_NAME.fullmatch(result)), f"{label} is not a qualified Lean name: {result}")
    return result


def lean_name_list(value: Any, label: str) -> list[str]:
    require(isinstance(value, list), f"{label} must be an array")
    result = [lean_name(name, f"{label}[{index}]") for index, name in enumerate(value)]
    require(len(result) == len(set(result)), f"{label} contains duplicates")
    return result


def validate_classification(value: Any, label: str) -> None:
    require(isinstance(value, dict), f"{label} must be an object")
    require(set(value) == set(AXES), f"{label} must have exactly the seven axes")
    for axis in AXES:
        nonempty_string(value[axis], f"{label}.{axis}")


def family_number(family_id: str) -> int:
    match = re.match(r"^EQC-([0-9]{3})-", family_id)
    require(match is not None, f"invalid family id: {family_id}")
    return int(match.group(1))


def validate_schema(root: Path, schema_path: Path) -> None:
    schema = load_json(resolve(root, schema_path))
    require(
        schema.get("$schema") == "https://json-schema.org/draft/2020-12/schema",
        "registry schema must use JSON Schema draft 2020-12",
    )
    require(schema.get("type") == "object", "registry schema root must be an object")
    require(schema.get("additionalProperties") is False, "registry schema root must be closed")


def validate_cohort(root: Path) -> tuple[dict[str, Any], list[tuple[str, str]]]:
    cohort_file = resolve(root, COHORT_PATH)
    cohort = load_json(cohort_file)
    checksum = sha256_file(cohort_file)
    require(checksum == FROZEN_SHA256, f"frozen cohort checksum changed: {checksum}")
    sidecar = resolve(root, COHORT_SIDECAR).read_text(encoding="utf-8").split()
    require(bool(sidecar) and sidecar[0] == FROZEN_SHA256, "frozen cohort sidecar disagrees")
    require(cohort.get("manifestKind") == "goal1-comparison-cohort", "wrong cohort kind")
    families = cohort.get("families")
    require(isinstance(families, list) and len(families) == 51, "cohort must have 51 families")

    flattened: list[tuple[str, str]] = []
    family_ids: list[str] = []
    empty_prefixes: list[str] = []
    expected_family_keys = {
        "id",
        "slug",
        "evidence",
        "classification",
        "provisionalDisposition",
        "primaryOwner",
        "consumerStages",
        "declarations",
    }
    for index, family in enumerate(families, start=1):
        require(isinstance(family, dict), f"cohort family {index} is not an object")
        require(set(family) == expected_family_keys, f"cohort family {index} fields changed")
        family_id = nonempty_string(family["id"], f"cohort family {index}.id")
        require(family_number(family_id) == index, f"cohort family order differs at {family_id}")
        family_ids.append(family_id)
        validate_classification(family["classification"], f"cohort {family_id}.classification")
        declarations = family["declarations"]
        require(isinstance(declarations, list), f"cohort {family_id}.declarations must be an array")
        if not declarations:
            empty_prefixes.append(family_id[:7])
        for declaration in declarations:
            flattened.append((family_id, lean_name(declaration, f"cohort {family_id} declaration")))

    names = [declaration for _, declaration in flattened]
    require(len(flattened) == 936, f"cohort declaration count is {len(flattened)}, expected 936")
    require(len(names) == len(set(names)), "cohort declarations are not uniquely assigned")
    require(tuple(empty_prefixes) == EMPTY_FAMILY_IDS, f"unexpected empty families: {empty_prefixes}")
    require(len(set(family_ids)) == 51, "cohort family IDs are not unique")
    return cohort, flattened


def declaration_names(path: Path) -> list[str]:
    namespace: list[str] = []
    names: list[str] = []
    block_comment_depth = 0
    declaration_pattern = re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)?"
        r"(?:(?:public|protected|noncomputable)\s+)*"
        r"(?:def|theorem|lemma|abbrev|structure|instance)\s+([A-Za-z0-9_.']+)"
    )
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        # Declaration-like prose in Lean doc comments must never enter a
        # source-order manifest. Lean block comments nest, so remove them with
        # a tiny depth-aware scanner rather than a line-based regular
        # expression.
        code: list[str] = []
        cursor = 0
        while cursor < len(raw_line):
            token = raw_line[cursor : cursor + 2]
            if token == "/-":
                block_comment_depth += 1
                cursor += 2
            elif token == "-/" and block_comment_depth:
                block_comment_depth -= 1
                cursor += 2
            elif block_comment_depth:
                cursor += 1
            else:
                code.append(raw_line[cursor])
                cursor += 1
        line = "".join(code)
        namespace_match = re.match(r"^namespace\s+([A-Za-z0-9_.']+)\s*$", line)
        if namespace_match:
            namespace.extend(namespace_match.group(1).split("."))
            continue
        end_match = re.match(r"^end\s+([A-Za-z0-9_.']+)\s*$", line)
        if end_match:
            parts = end_match.group(1).split(".")
            if namespace[-len(parts) :] == parts:
                del namespace[-len(parts) :]
            continue
        declaration_match = declaration_pattern.match(line)
        if declaration_match and not line.lstrip().startswith("private "):
            names.append(".".join([*namespace, *declaration_match.group(1).split(".")]))
    return names


def extract_axiom_targets(path: Path) -> list[str]:
    namespace: list[str] = []
    targets: list[str] = []
    pending = False
    for line in path.read_text(encoding="utf-8").splitlines():
        namespace_match = re.match(r"^namespace\s+([A-Za-z0-9_.']+)\s*$", line)
        if namespace_match:
            namespace.extend(namespace_match.group(1).split("."))
            continue
        end_match = re.match(r"^end\s+([A-Za-z0-9_.']+)\s*$", line)
        if end_match:
            parts = end_match.group(1).split(".")
            if namespace[-len(parts) :] == parts:
                del namespace[-len(parts) :]
            continue
        text = line.strip()
        if pending:
            if text:
                target = text.split()[0]
                pending = False
            else:
                continue
        else:
            match = re.match(r"^#print\s+axioms(?:\s+([A-Za-z0-9_.']+))?", text)
            if not match:
                continue
            if match.group(1) is None:
                pending = True
                continue
            target = match.group(1)
        if target.startswith("QuaternionicComputing."):
            targets.append(target)
        elif "." not in target and namespace:
            targets.append(".".join([*namespace, target]))
        else:
            targets.append(target)
    require(not pending, f"unterminated #print axioms command in {path}")
    return targets


def audit_target_sets(root: Path) -> tuple[set[str], set[str]]:
    root_targets = set(extract_axiom_targets(resolve(root, AXIOM_AUDIT_PATH)))
    all_targets = set(root_targets)
    for path in (root / "QuaternionicComputing").rglob("*Audit.lean"):
        all_targets.update(extract_axiom_targets(path))
    return root_targets, all_targets


def validate_manifest(
    root: Path, frozen_declarations: Iterable[str]
) -> tuple[dict[str, Any], set[str], set[str]]:
    manifest = load_json(resolve(root, MANIFEST_PATH))
    require(manifest.get("manifestKind") == "goal2-semantic-api", "wrong Goal 2 manifest kind")
    contract = manifest.get("itemContract")
    require(isinstance(contract, dict), "Goal 2 manifest itemContract is absent")
    required = contract.get("requiredFields")
    axes = contract.get("classificationAxes")
    require(isinstance(required, list), "manifest requiredFields must be an array")
    require(tuple(axes or []) == AXES, "manifest classification axes changed")
    items = manifest.get("items")
    require(isinstance(items, list), "Goal 2 manifest items must be an array")
    require(len(items) >= STAGE10_MANIFEST_COUNT, "Goal 2 manifest lost its Stage 10 prefix")

    names: list[str] = []
    consumers: list[str] = []
    direct_names: list[str] = []
    for index, item in enumerate(items):
        label = f"manifest item {index}"
        require(isinstance(item, dict), f"{label} is not an object")
        require(set(item) == set(required), f"{label} fields differ from itemContract")
        declaration = lean_name(item.get("declaration"), f"{label}.declaration")
        names.append(declaration)
        for field in ("relation", "owner", "consumer", "axiomAudit"):
            nonempty_string(item.get(field), f"{label}.{field}")
        consumers.append(lean_name(item["consumer"], f"{label}.consumer"))
        validate_classification(item.get("classification"), f"{label}.classification")
        if item["axiomAudit"] == DIRECT_LABEL:
            direct_names.append(declaration)

    require(len(names) == len(set(names)), "Goal 2 manifest declarations are duplicated")
    require(
        not (set(names) & set(frozen_declarations)),
        "Goal 2 manifest overlaps the immutable Goal 1 cohort",
    )
    prefix1100 = structural_hash(items[:STAGE9C_MANIFEST_COUNT])
    require(prefix1100 == STAGE9C_STRUCTURAL_SHA256, f"first-1100 manifest hash changed: {prefix1100}")
    prefix1269 = structural_hash(items[:STAGE10_MANIFEST_COUNT])
    require(prefix1269 == STAGE10_STRUCTURAL_SHA256, f"first-1269 manifest hash changed: {prefix1269}")

    stage10_source = [
        name
        for relative in STAGE10_SOURCE_FILES
        for name in declaration_names(resolve(root, relative))
    ]
    require(len(stage10_source) == 169, f"Stage 10 public source count is {len(stage10_source)}")
    require(
        names[STAGE9C_MANIFEST_COUNT:STAGE10_MANIFEST_COUNT] == stage10_source,
        "Stage 10 manifest/source order differs",
    )
    suffix = names[STAGE10_MANIFEST_COUNT:]
    existing_results = root / "QuaternionicComputing/Semantics/ExistingResults.lean"
    if suffix:
        require(existing_results.is_file(), "manifest has a Stage 11 suffix but ExistingResults.lean is absent")
        require(suffix == declaration_names(existing_results), "Stage 11 manifest/source order differs")

    root_targets, _ = audit_target_sets(root)
    intersection = set(names) & root_targets
    require(set(direct_names) == intersection, "manifest direct labels differ from root-audit intersection")
    baseline = items[:STAGE10_MANIFEST_COUNT]
    baseline_consumers = {item["consumer"] for item in baseline}
    baseline_direct = [item for item in baseline if item["axiomAudit"] == DIRECT_LABEL]
    require(len(baseline_consumers) == 164, "Stage 10 consumer baseline changed")
    require(len(baseline_direct) == 350, "corrected Stage 10 direct-audit baseline changed")
    return manifest, set(names), set(consumers)


def validate_import_boundaries(root: Path) -> None:
    import_audit = re.compile(r"^\s*(?:public\s+)?import\s+.*Audit\s*$", re.MULTILINE)
    public_root = resolve(root, PUBLIC_ROOT_PATH).read_text(encoding="utf-8")
    require(not import_audit.search(public_root), "public root imports an audit module")
    for path in (root / "QuaternionicComputing").rglob("*.lean"):
        if "Audit" in path.stem:
            continue
        text = path.read_text(encoding="utf-8")
        require(not import_audit.search(text), f"stable leaf imports an audit module: {path.relative_to(root)}")


def validate_audit(value: Any, label: str, root_targets: set[str], all_targets: set[str]) -> None:
    require(isinstance(value, dict) and set(value) == {"mode", "endpoint"}, f"{label} has invalid fields")
    mode = value.get("mode")
    require(mode in AUDIT_MODES, f"{label}.mode is invalid: {mode}")
    endpoint = value.get("endpoint")
    if mode == "notApplicable":
        require(endpoint is None, f"{label}.endpoint must be null when notApplicable")
        return
    endpoint_name = lean_name(endpoint, f"{label}.endpoint")
    if mode == "directRoot":
        require(endpoint_name in root_targets, f"{label} direct endpoint is absent from AxiomAudit")
    elif mode == "localEndpoint":
        require(endpoint_name in all_targets, f"{label} endpoint is absent from maintained axiom audits")
        require(
            endpoint_name not in root_targets,
            f"{label} is marked localEndpoint but is directly audited in AxiomAudit",
        )
    else:
        require(endpoint_name in all_targets, f"{label} endpoint is absent from maintained axiom audits")


def validate_evidence_record(
    record: dict[str, Any],
    label: str,
    *,
    family: bool,
    root_targets: set[str],
    all_targets: set[str],
) -> None:
    semantic_class = record.get("semanticClass")
    require(semantic_class in SEMANTIC_CLASSES, f"{label}.semanticClass is invalid")
    evidence_mode = record.get("evidenceMode")
    allowed = EVIDENCE_MODES if family else DECLARATION_EVIDENCE_MODES
    require(evidence_mode in allowed, f"{label}.evidenceMode is invalid")
    relations = lean_name_list(record.get("strongestRelations"), f"{label}.strongestRelations")
    proofs = lean_name_list(record.get("proofDeclarations"), f"{label}.proofDeclarations")
    lean_name_list(record.get("weakerTheorems"), f"{label}.weakerTheorems")
    lean_name_list(record.get("strictnessWitnesses"), f"{label}.strictnessWitnesses")
    consumer = record.get("consumer")
    if consumer is not None:
        lean_name(consumer, f"{label}.consumer")
    validate_audit(record.get("audit"), f"{label}.audit", root_targets, all_targets)
    nonempty_string(record.get("finalDisposition"), f"{label}.finalDisposition")
    nonempty_string(record.get("goal3Boundary"), f"{label}.goal3Boundary")

    if evidence_mode in PROOF_MODES:
        require(bool(proofs), f"{label} proof-bearing evidence has no proof declaration")
        require(isinstance(consumer, str), f"{label} proof-bearing evidence has no consumer")
        require(record["audit"]["mode"] != "notApplicable", f"{label} proof is unaudited")
    if evidence_mode in {"proofBearingRelation", "proofBearingCertificate"}:
        require(bool(relations), f"{label} has no strongest relation")
    if evidence_mode in NONBEHAVIORAL_MODES:
        require(not relations, f"{label} nonbehavioral evidence names a behavioral relation")
    if evidence_mode == "resourceDisposition":
        require(semantic_class == "resourceClaim", f"{label} resource disposition has wrong class")
    if evidence_mode == "counterexample":
        require(semantic_class == "diagnosticCounterexample", f"{label} counterexample has wrong class")


def validate_registry(
    root: Path,
    registry_path: Path,
    cohort: dict[str, Any],
    flattened: list[tuple[str, str]],
) -> dict[str, Any]:
    registry = load_json(resolve(root, registry_path))
    require(set(registry) == REGISTRY_TOP_KEYS, "registry top-level fields differ from schema")
    require(registry.get("schemaVersion") == 1, "registry schemaVersion must be 1")
    require(
        registry.get("registryKind") == "goal2-final-classification-overlay",
        "registryKind is incorrect",
    )
    require(tuple(registry.get("classificationAxes", [])) == AXES, "registry axes differ")
    expected_inputs = {
        "frozenCohort": {
            "path": str(COHORT_PATH),
            "sha256": FROZEN_SHA256,
            "familyCount": 51,
            "declarationCount": 936,
        },
        "semanticAPI": {
            "path": str(MANIFEST_PATH),
            "baselineCount": STAGE10_MANIFEST_COUNT,
            "baselineStructuralSha256": STAGE10_STRUCTURAL_SHA256,
        },
    }
    require(registry.get("inputs") == expected_inputs, "registry input fingerprints differ")

    root_targets, all_targets = audit_target_sets(root)
    frozen_families = cohort["families"]
    families = registry.get("families")
    require(isinstance(families, list) and len(families) == 51, "registry must have 51 families")
    for index, (record, frozen) in enumerate(zip(families, frozen_families, strict=True)):
        label = f"registry family {index + 1}"
        require(isinstance(record, dict) and set(record) == FAMILY_KEYS, f"{label} fields differ")
        require(record.get("id") == frozen["id"], f"{label} ID/order differs from cohort")
        require(record.get("slug") == frozen["slug"], f"{label} slug differs from cohort")
        number = family_number(frozen["id"])
        expected_origin = "goal1Public" if number <= 41 else "goal1Boundary" if number == 42 else "sourceOnly"
        require(record.get("origin") == expected_origin, f"{label} origin must be {expected_origin}")
        expected_count = len(frozen["declarations"])
        require(record.get("declarationCount") == expected_count, f"{label} declaration count differs")
        validate_classification(record.get("classification"), f"{label}.classification")
        require(record.get("finalStatus") in FINAL_STATUSES, f"{label}.finalStatus is invalid")
        obstruction = record.get("obstruction")
        require(obstruction is None or (isinstance(obstruction, str) and bool(obstruction)), f"{label}.obstruction is invalid")
        validate_evidence_record(
            record,
            label,
            family=True,
            root_targets=root_targets,
            all_targets=all_targets,
        )
        if expected_origin in {"goal1Boundary", "sourceOnly"}:
            require(expected_count == 0, f"{label} empty-family origin has declarations")
        if record["evidenceMode"] == "sourceOnlyObstruction":
            require(expected_origin == "sourceOnly", f"{label} source obstruction has wrong origin")
            require(not record["proofDeclarations"], f"{label} source obstruction has proof declarations")
            require(record["consumer"] is None, f"{label} source obstruction has a consumer")
            require(record["audit"]["mode"] == "notApplicable", f"{label} source obstruction has an audit")
            require(isinstance(obstruction, str) and bool(obstruction), f"{label} lacks an obstruction")
        if record["finalStatus"] in {"intentionallyExcluded", "unresolved"}:
            require(isinstance(obstruction, str) and bool(obstruction), f"{label} terminal status lacks obstruction")

    family_by_number = {family_number(record["id"]): record for record in families}
    require(
        family_by_number[42]["semanticClass"] == "approximationBoundary"
        and family_by_number[42]["finalStatus"] == "proved",
        "EQC-042 must record the proved Stage 10 metric boundary",
    )
    require(
        any(name.endswith("RealStatePhaseEq") for name in family_by_number[43]["strongestRelations"]),
        "EQC-043 must record the proved real-sign state relation",
    )
    require(
        any(name.endswith("SameBasisBehavior") for name in family_by_number[44]["strongestRelations"]),
        "EQC-044 must record the certified classical-basis relation",
    )
    for number in range(45, 52):
        record = family_by_number[number]
        require(
            record["origin"] == "sourceOnly"
            and record["evidenceMode"] == "sourceOnlyObstruction"
            and record["finalStatus"] == "unresolved",
            f"EQC-{number:03d} must retain its explicit source-only Goal 3 obstruction",
        )

    explicitly_nonbehavioral = {6, 15, 17, 18, 20, 21, 22, 23, 24, 29, 41}
    for number in explicitly_nonbehavioral:
        record = family_by_number[number]
        require(
            record["evidenceMode"] in NONBEHAVIORAL_MODES | {"counterexample"},
            f"EQC-{number:03d} is algebraic/structural/resource support, not behavioral equivalence",
        )

    declarations = registry.get("declarations")
    require(isinstance(declarations, list) and len(declarations) == 936, "registry must have 936 declarations")
    actual_pairs: list[tuple[str, str]] = []
    for index, record in enumerate(declarations):
        label = f"registry declaration {index}"
        require(isinstance(record, dict) and set(record) == DECLARATION_KEYS, f"{label} fields differ")
        declaration = lean_name(record.get("declaration"), f"{label}.declaration")
        family_id = nonempty_string(record.get("familyId"), f"{label}.familyId")
        actual_pairs.append((family_id, declaration))
        validate_classification(record.get("classification"), f"{label}.classification")
        validate_evidence_record(
            record,
            label,
            family=False,
            root_targets=root_targets,
            all_targets=all_targets,
        )
        if declaration in root_targets:
            require(
                record["audit"]
                == {"mode": "directRoot", "endpoint": declaration},
                f"{label} is directly root-audited and must record its own endpoint",
            )
    require(actual_pairs == flattened, "registry declaration set, family assignment, or order differs")
    require(len({name for _, name in actual_pairs}) == 936, "registry declarations are duplicated")

    declarations_by_number: dict[int, list[dict[str, Any]]] = {}
    for record in declarations:
        declarations_by_number.setdefault(family_number(record["familyId"]), []).append(record)
    for number in range(1, 41):
        require(
            all(
                record["classification"]
                == family_by_number[number]["classification"]
                for record in declarations_by_number[number]
            ),
            f"EQC-{number:03d} family axes drift from its homogeneous declaration axes",
        )
    require(
        "arity, gate count, dense description size"
        in family_by_number[41]["classification"]["subject"],
        "EQC-041 family axes must summarize its heterogeneous resource subfamilies",
    )
    require(
        "metric error budgets" in family_by_number[42]["classification"]["subject"]
        and "zero-budget exact" in family_by_number[42]["classification"]["exactness"],
        "EQC-042 family axes must record the final Stage 10 approximation boundary",
    )
    require(
        "RealRay" in family_by_number[43]["classification"]["subject"]
        and "real unit sign" in family_by_number[43]["classification"]["phase"],
        "EQC-043 family axes must record the proved real-sign quotient",
    )
    require(
        "basis-permutation implementation certificates"
        in family_by_number[44]["classification"]["subject"]
        and "every computational-basis input"
        in family_by_number[44]["classification"]["inputScope"],
        "EQC-044 family axes must record certified all-basis-input behavior",
    )
    require(
        "every source quaternionic pure state"
        in family_by_number[47]["classification"]["inputScope"]
        and "mixed" not in family_by_number[47]["classification"]["inputScope"],
        "EQC-047 must retain its pure-state reduced-matrix scope",
    )
    for record in declarations_by_number[1]:
        scope = record["classification"]["inputScope"]
        require(
            "raw" in scope and "normalized" in scope,
            "EQC-001 overlay must retain the raw witness and the checked normalized repair",
        )
    for record in declarations_by_number[14]:
        scope = record["classification"]["inputScope"]
        require(
            "every computational-basis input" in scope and "ground" in scope,
            "EQC-014 overlay must record both certified all-input behavior and the ground-input theorem",
        )
    for record in declarations_by_number[28]:
        scope = record["classification"]["inputScope"]
        require(
            "ground" in scope and "all normalized pure" in scope,
            "EQC-028 overlay must distinguish fixed-ground agreement from all-pure-input failure",
        )
        disposition = record["finalDisposition"]
        require(
            "one fixed normalized ground input" in disposition
            and "equality over all normalized pure inputs fails" in disposition,
            "EQC-028 disposition must state a failed universal relation, not that every pure input differs",
        )

    translation_work_name = (
        "QuaternionicComputing.Circuit.OrderedCircuit."
        "translationWork_le_gateCount_mul"
    )
    translation_work = next(
        record for record in declarations if record["declaration"] == translation_work_name
    )
    require(
        translation_work["proofDeclarations"] == [translation_work_name]
        and "per-occurrence translation work"
        in translation_work["classification"]["subject"]
        and translation_work["audit"]
        == {"mode": "directRoot", "endpoint": translation_work_name},
        "translationWork_le_gateCount_mul must retain its generic work-bound classification",
    )
    translation_definition_name = (
        "QuaternionicComputing.Circuit.OrderedCircuit.translationWork"
    )
    translation_definition = next(
        record
        for record in declarations
        if record["declaration"] == translation_definition_name
    )
    require(
        translation_definition["proofDeclarations"] == [translation_work_name]
        and "sum of a supplied natural-number work function"
        in translation_definition["classification"]["subject"]
        and translation_definition["audit"]
        == {"mode": "directRoot", "endpoint": translation_work_name},
        "translationWork must retain its exact per-occurrence sum classification",
    )

    inverse_arity_name = (
        "QuaternionicComputing.Circuit.PlacedGate."
        "localArity_le_log_four_of_denseEntrySlots_le"
    )
    inverse_arity = next(
        record for record in declarations if record["declaration"] == inverse_arity_name
    )
    require(
        inverse_arity["proofDeclarations"] == [inverse_arity_name]
        and "inverse arity bound" in inverse_arity["classification"]["subject"]
        and "localArity" in inverse_arity["classification"]["observationScope"]
        and inverse_arity["audit"]
        == {"mode": "directRoot", "endpoint": inverse_arity_name},
        "localArity_le_log_four_of_denseEntrySlots_le must retain its inverse arity-bound classification",
    )
    return registry


def validate_consumer_mentions(root: Path, registry: dict[str, Any]) -> None:
    existing_audit = root / "QuaternionicComputing/Semantics/ExistingResultsAudit.lean"
    if not existing_audit.is_file():
        return
    text = existing_audit.read_text(encoding="utf-8")
    blocks = {
        match.group(1): match.group(0)
        for match in re.finditer(
            r"(?ms)^theorem\s+([A-Za-z0-9_']+)\b.*?(?=^/--|^/-!|^#print|^end\s|\Z)",
            text,
        )
    }
    for record in registry["declarations"]:
        consumer = record.get("consumer")
        if not isinstance(consumer, str) or ".ExistingResultsAudit." not in consumer:
            continue
        consumer_short = consumer.rsplit(".", 1)[-1]
        require(consumer_short in blocks, f"missing ExistingResultsAudit consumer {consumer}")
        declaration_short = record["declaration"].rsplit(".", 1)[-1]
        require(
            declaration_short in blocks[consumer_short],
            f"{consumer} does not textually exercise {record['declaration']}",
        )


def registry_table_cell(value: str) -> str:
    """Normalize prose for one single-line Markdown table cell."""
    return " ".join(value.split()).replace("|", r"\|")


def render_registry_family_table(registry: dict[str, Any]) -> str:
    lines = [
        REGISTRY_TABLE_START,
        "| ID | Final status | Semantic class | Evidence mode | Strongest checked result | Goal 3 boundary |",
        "|---|---|---|---|---|---|",
    ]
    for family in registry["families"]:
        proofs = family["proofDeclarations"]
        proof_cell = "<br>".join(f"`{name}`" for name in proofs) if proofs else "—"
        lines.append(
            "| "
            f"`{family['id']}` | `{family['finalStatus']}` | "
            f"`{family['semanticClass']}` | `{family['evidenceMode']}` | "
            f"{proof_cell} | {registry_table_cell(family['goal3Boundary'])} |"
        )
    lines.append(REGISTRY_TABLE_END)
    return "\n".join(lines)


def validate_documented_registry_table(root: Path, registry: dict[str, Any]) -> None:
    path = resolve(root, CLASSIFICATION_DOC_PATH)
    text = path.read_text(encoding="utf-8")
    require(text.count(REGISTRY_TABLE_START) == 1, "classification document lacks one registry-table start marker")
    require(text.count(REGISTRY_TABLE_END) == 1, "classification document lacks one registry-table end marker")
    start = text.index(REGISTRY_TABLE_START)
    end = text.index(REGISTRY_TABLE_END, start) + len(REGISTRY_TABLE_END)
    actual = text[start:end]
    expected = render_registry_family_table(registry)
    require(actual == expected, "documented final 51-family table differs from the checked registry")


def run_lean_checks(
    root: Path,
    *,
    registry_required: bool,
    registry_path: Path,
) -> None:
    kinds = ["goal1-names", "goal2-names", "goal2-consumers"]
    if registry_required:
        kinds.append("registry-evidence")
    with tempfile.TemporaryDirectory(prefix="goal2-registry-") as directory:
        temporary = Path(directory)
        for kind in kinds:
            source = lean_checks.render_kind(
                kind,
                root=root,
                cohort_path=COHORT_PATH,
                manifest_path=MANIFEST_PATH,
                registry_path=registry_path,
            )
            target = temporary / (kind.replace("-", "_") + ".lean")
            target.write_text(source, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", "-DwarningAsError=true", str(target)],
                cwd=root,
                text=True,
                capture_output=True,
                check=False,
            )
            if result.returncode != 0:
                output = (result.stdout + result.stderr)[-8000:]
                raise ValidationError(f"generated Lean check {kind} failed:\n{output}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="validate the Goal 2 classification registry and its immutable inputs"
    )
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--registry", type=Path, default=REGISTRY_PATH)
    parser.add_argument("--schema", type=Path, default=SCHEMA_PATH)
    parser.add_argument(
        "--self-check",
        action="store_true",
        help="validate maintained inputs without requiring the not-yet-created final registry",
    )
    parser.add_argument(
        "--skip-lean",
        action="store_true",
        help="skip temporary generated Lean name and consumer checks",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo_root.resolve()
    try:
        validate_schema(root, args.schema)
        cohort, flattened = validate_cohort(root)
        manifest, manifest_names, manifest_consumers = validate_manifest(
            root, (declaration for _, declaration in flattened)
        )
        validate_import_boundaries(root)
        registry: dict[str, Any] | None = None
        if not args.self_check:
            registry = validate_registry(root, args.registry, cohort, flattened)
            validate_consumer_mentions(root, registry)
            validate_documented_registry_table(root, registry)
        if not args.skip_lean:
            run_lean_checks(
                root,
                registry_required=not args.self_check,
                registry_path=args.registry,
            )
    except ValidationError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1

    direct_count = sum(
        item.get("axiomAudit") == DIRECT_LABEL for item in manifest["items"]
    )
    mode = "inputs-only" if args.self_check else "complete-registry"
    print(
        "PASS "
        f"mode={mode} families=51 frozen=936 empty=10 "
        f"goal2={len(manifest_names)} consumers={len(manifest_consumers)} "
        f"direct={direct_count} axes=7"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
