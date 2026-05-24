#include "elaborator/sequence_match_attach.h"

#include "elaborator/sequence_degeneracy.h"

namespace delta {

bool IsAttachableSubroutineKind(AttachableSubroutineKind /*k*/) {
  // §16.11: every kind enumerated by the LRM (task, task method, void
  // function, void function method, system task) is attachable. The
  // enumeration is exhaustive — non-listed callable shapes (e.g. a non-void
  // function) are not reachable through this enum.
  return true;
}

bool IsSequenceMatchItemAttachLegal(SequenceMatchClass seq_class) {
  // §16.11: it is an error to attach a sequence_match_item to a sequence
  // that admits an empty match. §16.12.22's classifier owns the predicate;
  // §16.12.22's kAdmitsOnlyEmpty is the rejected case, while the
  // nondegenerate class is allowed even though a few of its members may
  // also admit empty matches — §16.11's text scopes the prohibition to
  // sequences that "admit an empty match" as their characterization, which
  // §16.12.22 ties to the degenerate-only-empty class.
  return seq_class != SequenceMatchClass::kAdmitsOnlyEmpty &&
         seq_class != SequenceMatchClass::kAdmitsNoMatch;
}

bool IsArgPassingAllowedForAttachedCall(SubroutineArgPassing kind) {
  switch (kind) {
    case SubroutineArgPassing::kByValueInput:
    case SubroutineArgPassing::kByRef:
    case SubroutineArgPassing::kByConstRef:
      return true;
  }
  return false;
}

bool IsAutomaticArgUseAllowed(SubroutineArgPassing kind,
                              bool from_procedural_assertion,
                              bool is_constant) {
  // §16.11: from procedural code (§16.14.6.1), an automatic variable can be
  // passed only as a constant input. Outside procedural code, no path is
  // available. By-reference passing is never allowed for automatics.
  if (kind == SubroutineArgPassing::kByRef ||
      kind == SubroutineArgPassing::kByConstRef) {
    return false;
  }
  if (!from_procedural_assertion) return false;
  return is_constant;
}

bool IsLocalVarArgPassingLegal(bool local_var_in_arg_expr,
                               SubroutineArgPassing kind) {
  // §16.11: if a local variable appears in an actual argument expression,
  // that argument shall be passed by value. By-reference passing is
  // therefore illegal when the expression mentions a local variable; when
  // it does not, any of the three passing modes is fine.
  if (!local_var_in_arg_expr) return true;
  return kind == SubroutineArgPassing::kByValueInput;
}

AttachedSubroutineSchedulingRegion AttachedSubroutineRegion() {
  // §16.11: attached subroutine calls are scheduled like action blocks, in
  // the Reactive region.
  return AttachedSubroutineSchedulingRegion::kReactive;
}

bool AssertionEvalWaitsForAttachedSubroutine() {
  // §16.11: assertion evaluation does not wait on, or receive data back
  // from, any attached subroutine.
  return false;
}

bool AttachedSubroutineRunsAtEveryEndPoint() {
  // §16.11: all subroutine calls attached to a sequence are executed at
  // every end point of the sequence.
  return true;
}

bool AttachedSubroutineCallsExecuteInListOrder() {
  // §16.11: for each end point, the attached calls are executed in the
  // order they appear in the list.
  return true;
}

bool IsByValueInputArgumentTypeAllowed(bool type_allowed_in_16_6) {
  // §16.11: the gating predicate is exactly "is the type allowed in §16.6".
  return type_allowed_in_16_6;
}

bool ByValueArgumentUsesSampledValuesOfUnderlying() {
  // §16.11: by-value passing reads sampled values, not current values.
  return true;
}

bool ByValueArgumentValueIsConsistentWithSequenceMatch() {
  // §16.11: those sampled values match the ones used to evaluate the
  // sequence match the call is attached to.
  return true;
}

}  // namespace delta
