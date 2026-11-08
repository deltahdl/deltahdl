#include "elaborator/sequence_match_attach.h"

#include "elaborator/sequence_degeneracy.h"

namespace delta {

bool IsAttachableSubroutineKind(AttachableSubroutineKind) { return true; }

bool IsSequenceMatchItemAttachLegal(SequenceMatchClass seq_class) {
  return seq_class != SequenceMatchClass::kAdmitsOnlyEmpty &&
         seq_class != SequenceMatchClass::kAdmitsNoMatch;
}

bool IsArgPassingAllowedForAttachedCall(SubroutineArgPassing kind) {
  return kind != SubroutineArgPassing::kCopiedOut &&
         kind != SubroutineArgPassing::kCopiedInOut;
}

bool IsAutomaticArgUseAllowed(SubroutineArgPassing kind,
                              bool from_procedural_assertion,
                              bool is_constant) {
  if (kind == SubroutineArgPassing::kByRef ||
      kind == SubroutineArgPassing::kByConstRef) {
    return false;
  }
  if (!from_procedural_assertion) return false;
  return is_constant;
}

bool IsLocalVarArgPassingLegal(bool local_var_in_arg_expr,
                               SubroutineArgPassing kind) {
  if (!local_var_in_arg_expr) return true;
  return kind == SubroutineArgPassing::kByValueInput;
}

AttachedSubroutineSchedulingRegion AttachedSubroutineRegion() {
  return AttachedSubroutineSchedulingRegion::kReactive;
}

bool AssertionEvalWaitsForAttachedSubroutine() { return false; }

bool AttachedSubroutineRunsAtEveryEndPoint() { return true; }

bool AttachedSubroutineCallsExecuteInListOrder() { return true; }

bool IsByValueInputArgumentTypeAllowed(bool type_allowed_in_16_6) {
  return type_allowed_in_16_6;
}

bool ByValueArgumentUsesSampledValuesOfUnderlying() { return true; }

bool ByValueArgumentValueIsConsistentWithSequenceMatch() { return true; }

}  // namespace delta
