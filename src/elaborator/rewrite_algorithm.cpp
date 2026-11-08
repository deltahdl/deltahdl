#include "elaborator/rewrite_algorithm.h"

#include <optional>

namespace delta {

RewriteStage FirstRewriteStage() { return RewriteStage::kProperties; }

RewriteStage NextRewriteStage(RewriteStage stage) {
  switch (stage) {
    case RewriteStage::kProperties:
    case RewriteStage::kSequences:
      return RewriteStage::kSequences;
  }
  return RewriteStage::kSequences;
}

bool SequenceInstanceNeedsItemWrap(SequenceInstanceContext context) {
  switch (context) {
    case SequenceInstanceContext::kClockingEventOperand:
    case SequenceInstanceContext::kSequenceMethodOperand:
      return true;
    case SequenceInstanceContext::kOrdinary:
      return false;
  }
  return false;
}

std::optional<ActualArgumentSource> ActualArgumentFor(bool bound_in_instance,
                                                      bool default_declared) {
  if (bound_in_instance) return ActualArgumentSource::kBoundInInstance;
  if (default_declared) return ActualArgumentSource::kDeclaredDefault;
  return std::nullopt;
}

ReferenceReplacement ReplaceFormalReference(FormalKind kind,
                                            ActualNature actual) {
  switch (kind) {
    case FormalKind::kUntyped:
      if (actual == ActualNature::kDollarOrLvalue) {
        return ReferenceReplacement::kActualDirect;
      }
      return ReferenceReplacement::kItemCastInferredType;

    case FormalKind::kTypedNonMatching:
      if (actual == ActualNature::kCastingType) {
        return ReferenceReplacement::kItemCastToFormalType;
      }
      return ReferenceReplacement::kItemCastTypeOfFormal;

    case FormalKind::kTypedMatching:
      if (actual == ActualNature::kSequenceMethodOperand) {
        return ReferenceReplacement::kItemActual;
      }
      return ReferenceReplacement::kParenthesizedActual;

    case FormalKind::kLocalVariable:
      return ReferenceReplacement::kActualDirect;
  }
  return ReferenceReplacement::kActualDirect;
}

bool ReplacementMayStandAsMatchItemLvalue(ReferenceReplacement replacement) {
  switch (replacement) {
    case ReferenceReplacement::kItemCastToFormalType:
    case ReferenceReplacement::kItemCastTypeOfFormal:
      return false;
    case ReferenceReplacement::kActualDirect:
    case ReferenceReplacement::kItemCastInferredType:
    case ReferenceReplacement::kItemActual:
    case ReferenceReplacement::kParenthesizedActual:
      return true;
  }
  return true;
}

bool ParenthesizedActualNeedsParentheses(bool reference_already_parenthesized) {
  return !reference_already_parenthesized;
}

LocalVarSubstitution LocalVariableFlatten(LocalVarDirection direction) {
  LocalVarSubstitution sub;
  switch (direction) {
    case LocalVarDirection::kInput:
      sub.declaration_has_initializer = true;
      sub.appends_match_assignment = false;
      return sub;
    case LocalVarDirection::kInout:
      sub.declaration_has_initializer = true;
      sub.appends_match_assignment = true;
      return sub;
    case LocalVarDirection::kOutput:
      sub.declaration_has_initializer = false;
      sub.appends_match_assignment = true;
      return sub;
  }
  return sub;
}

LocalVarSubstitution PropertyLocalVariableFlatten() {
  return LocalVariableFlatten(LocalVarDirection::kInput);
}

FlattenedFormShape FlattenedForm(FlattenTarget target) {
  FlattenedFormShape shape;
  shape.local_var_declarations_ordered = false;
  shape.enclosed_in_parentheses = true;
  shape.appends_match_item_assignments = target == FlattenTarget::kSequence;
  shape.match_item_assignments_ordered = false;
  return shape;
}

}  // namespace delta
