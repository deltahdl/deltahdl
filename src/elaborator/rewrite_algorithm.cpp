#include "elaborator/rewrite_algorithm.h"

#include <optional>

namespace delta {

RewriteStage FirstRewriteStage() { return RewriteStage::kProperties; }

RewriteStage NextRewriteStage(RewriteStage stage) {
  // Properties are drained first, then sequences; sequences is the last stage.
  switch (stage) {
    case RewriteStage::kProperties:
    case RewriteStage::kSequences:
      return RewriteStage::kSequences;
  }
  return RewriteStage::kSequences;
}

bool SequenceInstanceNeedsItemWrap(SequenceInstanceContext context) {
  // step 2: the clocking_event and sequence_method_call occurrences keep the
  // flattened sequence usable as a named-sequence instance, so they are
  // wrapped with item(sequence'...). step 3: every other occurrence takes the
  // bare flattened sequence.
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
  // step 2: the bound actual comes first; the default stands in only where
  // no argument is bound to the formal.
  if (bound_in_instance) return ActualArgumentSource::kBoundInInstance;
  if (default_declared) return ActualArgumentSource::kDeclaredDefault;
  return std::nullopt;
}

ReferenceReplacement ReplaceFormalReference(FormalKind kind,
                                            ActualNature actual) {
  switch (kind) {
    case FormalKind::kUntyped:
      // step 3a: a `$` or variable_lvalue actual substitutes verbatim; step
      // 3b: any other actual is cast through its own self-determined type so
      // the substituted expression keeps that type's operations.
      if (actual == ActualNature::kDollarOrLvalue) {
        return ReferenceReplacement::kActualDirect;
      }
      return ReferenceReplacement::kItemCastInferredType;

    case FormalKind::kTypedNonMatching:
      // step 4a: when the formal's type is a casting_type the cast names that
      // type directly; step 4b: otherwise the cast goes through type(t).
      if (actual == ActualNature::kCastingType) {
        return ReferenceReplacement::kItemCastToFormalType;
      }
      return ReferenceReplacement::kItemCastTypeOfFormal;

    case FormalKind::kTypedMatching:
      // step 5a: a reference standing as a sequence_method_call operand is
      // wrapped with item so the method stays legal; step 5b: otherwise the
      // actual is simply parenthesized.
      if (actual == ActualNature::kSequenceMethodOperand) {
        return ReferenceReplacement::kItemActual;
      }
      return ReferenceReplacement::kParenthesizedActual;

    case FormalKind::kLocalVariable:
      // step 6 substitutes local variables through prepended declarations, not
      // in-place reference replacement; LocalVariableFlatten handles it. Treat
      // the reference itself as a direct substitution of the local name.
      return ReferenceReplacement::kActualDirect;
  }
  return ReferenceReplacement::kActualDirect;
}

bool ReplacementMayStandAsMatchItemLvalue(ReferenceReplacement replacement) {
  // step 4: the two casts through the formal's type are the references
  // §16.8.1 keeps out of the lvalue of a match-item assignment or increment;
  // the replacements of steps 3 and 5 carry no such note.
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
  // step 5b: the parentheses may be omitted only where the reference already
  // has its own.
  return !reference_already_parenthesized;
}

LocalVarSubstitution LocalVariableFlatten(LocalVarDirection direction) {
  LocalVarSubstitution sub;
  switch (direction) {
    case LocalVarDirection::kInput:
      // step 6a: "t f = a_f;" only — the value flows in, never back out.
      sub.declaration_has_initializer = true;
      sub.appends_match_assignment = false;
      return sub;
    case LocalVarDirection::kInout:
      // step 6b: "t f = a_f;" plus an appended "a_f = f" match-item
      // assignment so the updated value flows back to the actual.
      sub.declaration_has_initializer = true;
      sub.appends_match_assignment = true;
      return sub;
    case LocalVarDirection::kOutput:
      // step 6c: "t f;" (no initializer) plus the appended "a_f = f"
      // match-item assignment.
      sub.declaration_has_initializer = false;
      sub.appends_match_assignment = true;
      return sub;
  }
  return sub;
}

LocalVarSubstitution PropertyLocalVariableFlatten() {
  // flatten_property step 6: "t f = a_f;" for every local variable formal,
  // with nothing appended, which is the input shape of flatten_sequence.
  return LocalVariableFlatten(LocalVarDirection::kInput);
}

FlattenedFormShape FlattenedForm(FlattenTarget target) {
  FlattenedFormShape shape;
  // step 6: the declarations may be arranged in any order; step 7: the
  // result is enclosed in parentheses. Both hold for either target.
  shape.local_var_declarations_ordered = false;
  shape.enclosed_in_parentheses = true;
  // steps 6b and 6c: only flatten_sequence appends match-item assignments,
  // and the closing note has their order not matter.
  shape.appends_match_item_assignments = target == FlattenTarget::kSequence;
  shape.match_item_assignments_ordered = false;
  return shape;
}

}  // namespace delta
