require "json"

ROOT = File.expand_path(__dir__)
FILES = [
  "QuaternionicComputing/Semantics/Core.lean",
  "QuaternionicComputing/Semantics/Measurement.lean"
].freeze

DIRECT_AUDIT = %w[
  QuaternionicComputing.Semantics.ExactOperatorEq.mul
  QuaternionicComputing.Semantics.ExactCircuitEq.of_gatewise
  QuaternionicComputing.Semantics.ExactCircuitEq.append
  QuaternionicComputing.Semantics.OutputWeightEqAt.of_exact
  QuaternionicComputing.Semantics.BasisMeasurementEq.of_exact
  QuaternionicComputing.Semantics.PureInputBasisMeasurementEq.of_exact
  QuaternionicComputing.Semantics.basisMeasurementEq_iff_outputWeightEqAt_basis
  QuaternionicComputing.Semantics.outputWeightEqAt_basis_iff_column_weight
  QuaternionicComputing.Semantics.PureInputBasisMeasurementEq.basisMeasurementEq
  QuaternionicComputing.Semantics.basisWeightEq_iff_normalizedDistributionEq
  QuaternionicComputing.Semantics.BasisWeightEq.eventWeight_eq
  QuaternionicComputing.Semantics.BasisWeightEq.pushforward_eq
  QuaternionicComputing.Semantics.ExactCircuitEq.outputWeightEqAt
  QuaternionicComputing.Semantics.ExactCircuitEq.basisMeasurementEq
  QuaternionicComputing.Semantics.ExactCircuitEq.pureInputBasisMeasurementEq
].freeze

def declaration_names(path)
  stack = []
  names = []
  File.foreach(path) do |line|
    if (match = line.match(/^namespace\s+([A-Za-z0-9_.']+)\s*$/))
      stack.concat(match[1].split("."))
      next
    end
    if (match = line.match(/^end\s+([A-Za-z0-9_.']+)\s*$/))
      parts = match[1].split(".")
      if stack.last(parts.length) == parts
        parts.length.times { stack.pop }
      elsif (index = stack.rindex(parts.last))
        stack.slice!(index..)
      end
      next
    end
    match = line.match(/^\s*(?:@\[[^\]]+\]\s*)?(?:(?:public|protected|noncomputable)\s+)*(?:def|theorem|lemma|abbrev|structure)\s+([A-Za-z0-9_.']+)/)
    next unless match
    names << (stack + match[1].split(".")).join(".")
  end
  names
end

def relation_for(name)
  exact = "QuaternionicComputing.Semantics."
  case name
  when "#{exact}ExactOperatorEq.mul"
    "ExactOperatorEq multiplication congruence"
  when "#{exact}ExactCircuitEq.of_gatewise"
    "gatewise denotation equality→ExactCircuitEq"
  when "#{exact}ExactCircuitEq.append"
    "ExactCircuitEq append congruence"
  when "#{exact}OutputWeightEqAt.of_exact"
    "ExactOperatorEq→OutputWeightEqAt"
  when "#{exact}BasisMeasurementEq.of_exact"
    "ExactOperatorEq→BasisMeasurementEq"
  when "#{exact}PureInputBasisMeasurementEq.of_exact"
    "ExactOperatorEq→PureInputBasisMeasurementEq"
  when "#{exact}basisMeasurementEq_iff_outputWeightEqAt_basis"
    "BasisMeasurementEq↔basis-ket OutputWeightEqAt"
  when "#{exact}outputWeightEqAt_basis_iff_column_weight"
    "basis-ket OutputWeightEqAt↔column-weight equality"
  when "#{exact}PureInputBasisMeasurementEq.basisMeasurementEq"
    "PureInputBasisMeasurementEq→BasisMeasurementEq"
  when "#{exact}NormalizedDistributionEq.eventWeight_eq"
    "NormalizedDistributionEq→finite-event equality"
  when "#{exact}NormalizedDistributionEq.pushforward_eq"
    "NormalizedDistributionEq→deterministic-pushforward equality"
  when "#{exact}basisWeightEq_iff_normalizedDistributionEq"
    "BasisWeightEq↔NormalizedDistributionEq"
  when "#{exact}BasisWeightEq.normalizedDistributionEq"
    "BasisWeightEq→NormalizedDistributionEq"
  when "#{exact}BasisWeightEq.eventWeight_eq"
    "BasisWeightEq→finite-event equality"
  when "#{exact}BasisWeightEq.pushforward_eq"
    "BasisWeightEq→deterministic-pushforward equality"
  when "#{exact}BasisWeightEq.pushforward_weight_eq"
    "BasisWeightEq→deterministic-pushforward weight equality"
  when "#{exact}ExactCircuitEq.outputWeightEqAt"
    "ExactCircuitEq→OutputWeightEqAt"
  when "#{exact}ExactCircuitEq.basisMeasurementEq"
    "ExactCircuitEq→BasisMeasurementEq"
  when "#{exact}ExactCircuitEq.pureInputBasisMeasurementEq"
    "ExactCircuitEq→PureInputBasisMeasurementEq"
  else
    %w[
      ExactOperatorEq ExactCircuitEq BasisWeightEq OutputWeightEqAt
      BasisMeasurementEq PureInputBasisMeasurementEq NormalizedDistributionEq
    ].find { |relation| name.include?(relation) } ||
      raise("unclassified declaration #{name}")
  end
end

def consumer_for(name)
  exact = "QuaternionicComputing.Semantics."
  return "#{exact}CoreAudit.basisMeasurement_basisCharacterization" if
    name == "#{exact}basisMeasurementEq_iff_outputWeightEqAt_basis" ||
      name == "#{exact}outputWeightEqAt_basis_iff_column_weight"
  return "#{exact}CoreAudit.complexPureInput_to_basis" if
    name == "#{exact}PureInputBasisMeasurementEq.basisMeasurementEq"
  return "#{exact}CoreAudit.normalizedDistribution_api" if
    name.start_with?("#{exact}NormalizedDistributionEq") ||
      name == "#{exact}basisWeightEq_iff_normalizedDistributionEq" ||
      name.start_with?("#{exact}BasisWeightEq.normalizedDistributionEq") ||
      name.start_with?("#{exact}BasisWeightEq.eventWeight_eq") ||
      name.start_with?("#{exact}BasisWeightEq.pushforward")
  return "#{exact}CoreAudit.basisPreparation_fixedInputAgreement" if
    name == "#{exact}ExactCircuitEq.outputWeightEqAt"
  return "#{exact}CoreAudit.basisPreparation_basisAgreement" if
    name == "#{exact}ExactCircuitEq.basisMeasurementEq"
  return "#{exact}CoreAudit.basisPreparation_pureInputAgreement" if
    name == "#{exact}ExactCircuitEq.pureInputBasisMeasurementEq"
  return "#{exact}CoreAudit.exactOperator_api" if name.start_with?("#{exact}ExactOperatorEq")
  return "#{exact}CoreAudit.exactCircuit_api" if name.start_with?("#{exact}ExactCircuitEq")
  return "#{exact}CoreAudit.basisWeight_api" if name.start_with?("#{exact}BasisWeightEq")
  return "#{exact}CoreAudit.outputWeightEqAt_api" if name.start_with?("#{exact}OutputWeightEqAt")
  return "#{exact}CoreAudit.basisMeasurement_api" if name.start_with?("#{exact}BasisMeasurementEq")
  return "#{exact}CoreAudit.pureInputBasisMeasurement_api" if
    name.start_with?("#{exact}PureInputBasisMeasurementEq")
  raise "missing consumer for #{name}"
end

def axes(space, subject, input_scope, observation_scope,
    phase: "none", exactness: "exact", ancilla_policy: "none")
  {
    "space" => space,
    "subject" => subject,
    "inputScope" => input_scope,
    "observationScope" => observation_scope,
    "phase" => phase,
    "exactness" => exactness,
    "ancillaPolicy" => ancilla_policy
  }
end

def base_classification(name)
  case name
  when /ExactOperatorEq/
    axes("same scalar, row-index, and column-index types; no finiteness required",
      "matrix operators", "all entries of one fixed matrix type",
      "literal matrix equality")
  when /ExactCircuitEq/
    axes("same scalar and finite wire type",
      "ordered circuits", "whole chronological circuits",
      "literal equality of evaluated operators")
  when /BasisWeightEq/
    axes("same scalar-value and output-index types; no finiteness required",
      "state columns", "one pair of columns",
      "all computational-basis coordinate weights")
  when /OutputWeightEqAt/
    axes("same scalar/input/output types; only the input index is required finite",
      "matrix operators", "one explicitly supplied input column",
      "all computational-basis output weights")
  when /BasisMeasurementEq/
    axes("same scalar/input/output types; no finiteness required",
      "matrix operators", "all computational-basis input columns",
      "all computational-basis transition weights")
  when /PureInputBasisMeasurementEq/
    axes("same scalar/input/output types; only the input index is required finite",
      "matrix operators", "all normalized pure input columns",
      "all computational-basis output weights")
  when /NormalizedDistributionEq/
    axes("same scalar and finite outcome-index type",
      "normalized states and finite distributions", "one pair of normalized states",
      "full packaged finite-distribution equality")
  else
    raise "missing base classification for #{name}"
  end
end

def classification_for(name)
  exact = "QuaternionicComputing.Semantics."
  case name
  when "#{exact}ExactOperatorEq.mul"
    axes("same scalar with compatible matrix spaces and finite intermediate index",
      "matrix products", "two exact-equal pairs of compatible matrices",
      "literal equality of the two products")
  when "#{exact}ExactCircuitEq.of_gatewise"
    axes("same scalar and finite wire type", "ordered circuits",
      "every paired gate occurrence has equal denotation",
      "literal equality of chronological evaluations")
  when "#{exact}ExactCircuitEq.append"
    axes("same scalar and finite wire type", "ordered circuits",
      "two exact-equal pairs of chronological circuits",
      "literal equality after chronological append")
  when "#{exact}OutputWeightEqAt.of_exact"
    axes("same scalar/input/output types; finite input index", "matrix operators",
      "one explicitly supplied input column", "all output basis weights",
      exactness: "exact implication")
  when "#{exact}BasisMeasurementEq.of_exact"
    axes("same scalar/input/output types; no finiteness required", "matrix operators",
      "all computational-basis input columns", "all transition weights",
      exactness: "exact implication")
  when "#{exact}PureInputBasisMeasurementEq.of_exact"
    axes("same scalar/input/output types; finite input index", "matrix operators",
      "all normalized pure input columns", "all output basis weights",
      exactness: "exact implication")
  when "#{exact}basisMeasurementEq_iff_outputWeightEqAt_basis"
    axes("same scalar/input/output types; finite decidable input index", "matrix operators",
      "all computational-basis inputs, expressed as basis kets",
      "equivalence between transition weights and fixed-input output weights")
  when "#{exact}outputWeightEqAt_basis_iff_column_weight"
    axes("same scalar/input/output types; finite decidable input index", "matrix columns",
      "one named computational-basis input",
      "equivalence between basis-ket output weights and one column's weights")
  when "#{exact}PureInputBasisMeasurementEq.basisMeasurementEq"
    axes("same scalar/input/output types; finite decidable input index", "matrix operators",
      "all basis inputs, under an explicit proof that every basis ket has total weight one",
      "all computational-basis transition weights", exactness: "exact implication")
  when "#{exact}NormalizedDistributionEq.eventWeight_eq"
    axes("same scalar and finite outcome-index type", "finite distributions",
      "one pair of normalized states and every supplied finite event",
      "finite-event weight equality", exactness: "exact implication")
  when "#{exact}NormalizedDistributionEq.pushforward_eq"
    axes("same scalar and finite source/target outcome types", "finite distributions",
      "one pair of normalized states and a deterministic finite map",
      "full pushed-forward distribution equality", exactness: "exact implication",
      ancilla_policy: "named deterministic postprocessing map; no randomized decoder")
  when "#{exact}basisWeightEq_iff_normalizedDistributionEq"
    axes("same scalar and finite outcome-index type", "normalized states and finite distributions",
      "one pair of normalized states",
      "equivalence of all basis weights and full packaged distribution equality")
  when "#{exact}BasisWeightEq.normalizedDistributionEq"
    axes("same scalar and finite outcome-index type", "normalized states and finite distributions",
      "one pair of normalized states", "full packaged finite-distribution equality",
      exactness: "exact implication")
  when "#{exact}BasisWeightEq.eventWeight_eq"
    axes("same scalar and finite outcome-index type", "finite distributions",
      "one pair of normalized states and every supplied finite event",
      "finite-event weight equality", exactness: "exact implication")
  when "#{exact}BasisWeightEq.pushforward_eq"
    axes("same scalar and finite source/target outcome types", "finite distributions",
      "one pair of normalized states and a deterministic finite map",
      "full pushed-forward distribution equality", exactness: "exact implication",
      ancilla_policy: "named deterministic postprocessing map; no randomized decoder")
  when "#{exact}BasisWeightEq.pushforward_weight_eq"
    axes("same scalar and finite source/target outcome types", "finite distributions",
      "one pair of normalized states, a deterministic finite map, and one target outcome",
      "one pushed-forward output weight equality", exactness: "exact implication",
      ancilla_policy: "named deterministic postprocessing map; no randomized decoder")
  when "#{exact}ExactCircuitEq.outputWeightEqAt"
    axes("same scalar and finite wire type", "evaluated ordered circuits",
      "one explicitly supplied input column", "all output basis weights",
      exactness: "exact implication")
  when "#{exact}ExactCircuitEq.basisMeasurementEq"
    axes("same scalar and finite wire type", "evaluated ordered circuits",
      "all computational-basis input columns", "all transition weights",
      exactness: "exact implication")
  when "#{exact}ExactCircuitEq.pureInputBasisMeasurementEq"
    axes("same scalar and finite wire type", "evaluated ordered circuits",
      "all normalized pure input columns", "all output basis weights",
      exactness: "exact implication")
  else
    base_classification(name)
  end
end

items = FILES.flat_map do |relative|
  declaration_names(File.join(ROOT, relative)).map do |name|
    consumer = consumer_for(name)
    {
      "declaration" => name,
      "relation" => relation_for(name),
      "owner" => "goal-2/2-CORE",
      "consumer" => consumer,
      "axiomAudit" => DIRECT_AUDIT.include?(name) ?
        "direct #print axioms target in QuaternionicComputing/AxiomAudit.lean" :
        "transitively exercised by #{consumer}; direct release endpoint pending",
      "classification" => classification_for(name)
    }
  end
end

raise "expected 61 stable semantic declarations, found #{items.length}" unless items.length == 61
raise "duplicate API declarations" unless items.map { |item| item.fetch("declaration") }.uniq.length == 61
puts JSON.pretty_generate(items)
