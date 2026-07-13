#!/usr/bin/env python3
"""Render untracked Lean name checks for the Goal 2 registries.

The command writes only to stdout.  Callers may pipe a selected check to Lean
or place it in a temporary directory; this script never edits the repository.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_COHORT = Path("docs/Goal1ComparisonCohort.json")
DEFAULT_MANIFEST = Path("docs/Goal2SemanticAPIManifest.json")
DEFAULT_REGISTRY = Path("docs/Goal2ClassificationRegistry.json")

AUDIT_MODULES = (
    "QuaternionicComputing.Semantics.CoreAudit",
    "QuaternionicComputing.Semantics.StatePhaseAudit",
    "QuaternionicComputing.Semantics.OperatorPhase.ComplexRealAudit",
    "QuaternionicComputing.Semantics.OperatorPhase.QuaternionAudit",
    "QuaternionicComputing.State.RayAudit",
    "QuaternionicComputing.State.RayDescentAudit",
    "QuaternionicComputing.State.RealificationOrbitAudit",
    "QuaternionicComputing.Semantics.BasisBehaviorAudit",
    "QuaternionicComputing.Semantics.DensityAudit",
    "QuaternionicComputing.Semantics.ChannelAudit",
    "QuaternionicComputing.Semantics.HierarchyAudit",
    "QuaternionicComputing.Semantics.SimulationAudit",
    "QuaternionicComputing.Semantics.ApproximationAudit",
    "QuaternionicComputing.Semantics.ExistingResultsAudit",
    "QuaternionicComputing.Semantics.ProjectiveInputAudit",
)

KINDS = (
    "goal1-names",
    "registry-evidence",
    "goal2-names",
    "goal2-consumers",
)


def resolve_path(root: Path, path: Path) -> Path:
    return path if path.is_absolute() else root / path


def load_json(path: Path) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as handle:
            value = json.load(handle)
    except FileNotFoundError as exc:
        raise SystemExit(f"required JSON file is absent: {path}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid JSON in {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise SystemExit(f"expected a JSON object in {path}")
    return value


def unique(values: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for value in values:
        if value not in seen:
            seen.add(value)
            result.append(value)
    return result


def module_path(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def available_audit_modules(root: Path) -> list[str]:
    return [module for module in AUDIT_MODULES if module_path(root, module).is_file()]


def render(names: Iterable[str], imports: Iterable[str]) -> str:
    import_lines = [f"import {module}" for module in unique(imports)]
    check_lines = [f"#check {name}" for name in unique(names)]
    return "\n".join(import_lines + [""] + check_lines) + "\n"


def goal1_names(cohort: dict[str, Any]) -> list[str]:
    return [
        declaration
        for family in cohort.get("families", [])
        for declaration in family.get("declarations", [])
    ]


def goal2_names(manifest: dict[str, Any]) -> list[str]:
    return [item["declaration"] for item in manifest.get("items", [])]


def goal2_consumers(manifest: dict[str, Any]) -> list[str]:
    return unique(item["consumer"] for item in manifest.get("items", []))


def evidence_names(record: dict[str, Any]) -> Iterable[str]:
    for field in (
        "strongestRelations",
        "proofDeclarations",
        "weakerTheorems",
        "strictnessWitnesses",
    ):
        for name in record.get(field, []):
            yield name
    consumer = record.get("consumer")
    if isinstance(consumer, str):
        yield consumer
    audit = record.get("audit")
    if isinstance(audit, dict):
        endpoint = audit.get("endpoint")
        if isinstance(endpoint, str):
            yield endpoint


def registry_evidence(registry: dict[str, Any]) -> list[str]:
    records = list(registry.get("families", [])) + list(
        registry.get("declarations", [])
    )
    return unique(name for record in records for name in evidence_names(record))


def render_kind(
    kind: str,
    *,
    root: Path,
    cohort_path: Path = DEFAULT_COHORT,
    manifest_path: Path = DEFAULT_MANIFEST,
    registry_path: Path = DEFAULT_REGISTRY,
) -> str:
    if kind == "goal1-names":
        cohort = load_json(resolve_path(root, cohort_path))
        return render(goal1_names(cohort), ["QuaternionicComputing"])
    if kind == "goal2-names":
        manifest = load_json(resolve_path(root, manifest_path))
        return render(goal2_names(manifest), ["QuaternionicComputing"])
    if kind == "goal2-consumers":
        manifest = load_json(resolve_path(root, manifest_path))
        imports = ["QuaternionicComputing", *available_audit_modules(root)]
        return render(goal2_consumers(manifest), imports)
    if kind == "registry-evidence":
        registry = load_json(resolve_path(root, registry_path))
        imports = ["QuaternionicComputing", *available_audit_modules(root)]
        return render(registry_evidence(registry), imports)
    raise ValueError(f"unknown check kind: {kind}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="render one temporary Goal 2 Lean registry check to stdout"
    )
    parser.add_argument("--kind", choices=KINDS, required=True)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--cohort", type=Path, default=DEFAULT_COHORT)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    parser.add_argument(
        "--output",
        type=Path,
        help="write to this caller-supplied path outside the repository instead of stdout",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo_root.resolve()
    source = render_kind(
        args.kind,
        root=root,
        cohort_path=args.cohort,
        manifest_path=args.manifest,
        registry_path=args.registry,
    )
    if args.output is None:
        sys.stdout.write(source)
    else:
        output = args.output.resolve()
        if output.is_relative_to(root):
            raise SystemExit(
                f"refusing to write a generated check inside the repository: {output}"
            )
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(source, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
