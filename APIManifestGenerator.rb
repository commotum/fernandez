require "json"

ROOT = File.expand_path(__dir__)
FILES = [
  "QuaternionicComputing/Semantics/Core.lean",
  "QuaternionicComputing/Semantics/Measurement.lean",
  "QuaternionicComputing/Semantics/CoreAudit.lean"
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
  return "BasisMeasurementEq↔basis-OutputWeightEqAt" if
    name.include?("basisMeasurementEq_iff_outputWeightEqAt_basis")
  return "basis-OutputWeightEqAt↔column-weight-equality" if
    name.include?("outputWeightEqAt_basis_iff_column_weight")
  return "BasisWeightEq↔NormalizedDistributionEq" if
    name.include?("basisWeightEq_iff_normalizedDistributionEq")
  return "ExactCircuitEq→OutputWeightEqAt" if
    name.end_with?("ExactCircuitEq.outputWeightEqAt")
  return "ExactCircuitEq→BasisMeasurementEq" if
    name.end_with?("ExactCircuitEq.basisMeasurementEq")
  return "ExactCircuitEq→PureInputBasisMeasurementEq" if
    name.end_with?("ExactCircuitEq.pureInputBasisMeasurementEq")
  return "PureInputBasisMeasurementEq→BasisMeasurementEq" if
    name.end_with?("PureInputBasisMeasurementEq.basisMeasurementEq")
  %w[
    PureInputBasisMeasurementEq NormalizedDistributionEq
    BasisMeasurementEq OutputWeightEqAt BasisWeightEq
    ExactCircuitEq ExactOperatorEq
  ].find { |relation| name.include?(relation) } ||
    if name.include?("BasisKet_normalized")
      "basis-ket-normalization"
    elsif name.include?("emptyOperator_exact")
      "ExactOperatorEq"
    elsif name.include?("basisPreparation")
      "ExactCircuitEq/PureInputBasisMeasurementEq"
    elsif name.include?("complexPureInput_to_basis")
      "PureInputBasisMeasurementEq→BasisMeasurementEq"
    elsif name.include?("complexState_distribution_refl")
      "NormalizedDistributionEq"
    else
      raise "unclassified declaration #{name}"
    end
end

def classification(relation, audit)
  return {
    "space" => "same finite scalar/index space",
    "subject" => "diagnostic consumer",
    "inputScope" => "exact example scope",
    "observationScope" => "the relation named by the diagnostic",
    "phase" => "none",
    "exactness" => "exact",
    "ancillaPolicy" => "none"
  } if audit

  case relation
  when /ExactOperatorEq/
    subject = "matrix operator"
    input = "all entries of one fixed matrix type"
    observation = "literal matrix equality"
  when /ExactCircuitEq/
    subject = "ordered circuit"
    input = "whole chronological circuit"
    observation = "literal equality of evaluated operators"
  when /^BasisWeightEq/
    subject = "state columns"
    input = "one pair of columns"
    observation = "all computational-basis weights"
  when /^OutputWeightEqAt/
    subject = "matrix operators"
    input = "one explicitly supplied input column"
    observation = "all output computational-basis weights"
  when /^BasisMeasurementEq/
    subject = "matrix operators"
    input = "all computational-basis input columns"
    observation = "all computational-basis output weights"
  when /^PureInputBasisMeasurementEq/
    subject = "matrix operators"
    input = "all normalized pure input columns"
    observation = "all computational-basis output weights"
  when /^NormalizedDistributionEq/
    subject = "normalized states and finite distributions"
    input = "one pair of normalized pure states"
    observation = "full finite distribution, events, and deterministic pushforwards"
  else
    subject = "semantic bridge theorem"
    input = "the explicit scopes named by both linked relations"
    observation = "the linked computational-basis semantics"
  end
  {
    "space" => "same finite scalar/index space",
    "subject" => subject,
    "inputScope" => input,
    "observationScope" => observation,
    "phase" => "none",
    "exactness" => "exact",
    "ancillaPolicy" => "none"
  }
end

items = FILES.flat_map do |relative|
  audit = relative.end_with?("CoreAudit.lean")
  declaration_names(File.join(ROOT, relative)).map do |name|
    relation = relation_for(name)
    {
      "declaration" => name,
      "relation" => relation,
      "owner" => "goal-2/2-CORE",
      "consumer" => audit ?
        "diagnostic endpoint in QuaternionicComputing.Semantics.CoreAudit" :
        "QuaternionicComputing.Semantics.CoreAudit",
      "axiomAudit" => [
        "QuaternionicComputing.Semantics.ExactOperatorEq.mul",
        "QuaternionicComputing.Semantics.ExactCircuitEq.append",
        "QuaternionicComputing.Semantics.basisMeasurementEq_iff_outputWeightEqAt_basis",
        "QuaternionicComputing.Semantics.basisWeightEq_iff_normalizedDistributionEq",
        "QuaternionicComputing.Semantics.CoreAudit.complexPureInput_to_basis",
        "QuaternionicComputing.Semantics.CoreAudit.basisPreparation_pureInputAgreement"
      ].include?(name) ? "direct CoreAudit #print axioms endpoint" :
        "standard-foundation spot audit passed; release endpoint pending",
      "classification" => classification(relation, audit)
    }
  end
end

raise "duplicate API declarations" unless items.map { |item| item.fetch("declaration") }.uniq.length == items.length
puts JSON.pretty_generate(items)
