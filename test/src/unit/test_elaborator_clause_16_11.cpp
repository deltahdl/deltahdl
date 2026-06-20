#include <gtest/gtest.h>

#include "elaborator/sequence_degeneracy.h"
#include "elaborator/sequence_match_attach.h"

using namespace delta;

namespace {

TEST(AttachSubroutineCall, EmptyMatchSequenceRejectsAttachment) {
  // §16.11: it is an error to attach a sequence_match_item to a sequence
  // that admits an empty match. §16.12.22's classifier supplies the empty
  // notion: kAdmitsOnlyEmpty is the rejected case.
  EXPECT_FALSE(
      IsSequenceMatchItemAttachLegal(SequenceMatchClass::kAdmitsOnlyEmpty));
}

TEST(AttachSubroutineCall, NondegenerateSequenceAcceptsAttachment) {
  // §16.11 + §16.12.22: a sequence that admits at least one nonempty match
  // is the right shape for a subroutine_call or any sequence_match_item.
  EXPECT_TRUE(IsSequenceMatchItemAttachLegal(
      SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

TEST(AttachSubroutineCall, AutomaticByReferenceForbidden) {
  // §16.11: an automatic variable shall not be passed by reference under any
  // circumstance.
  EXPECT_FALSE(IsAutomaticArgUseAllowed(SubroutineArgPassing::kByRef,
                                        /*from_procedural_assertion=*/true,
                                        /*is_constant=*/true));
}

TEST(AttachSubroutineCall, AutomaticAsConstantInputFromProceduralAllowed) {
  // §16.11: an automatic variable may be passed as a constant input from a
  // subroutine call attached to a sequence inside a procedural assertion
  // (§16.14.6.1).
  EXPECT_TRUE(IsAutomaticArgUseAllowed(SubroutineArgPassing::kByValueInput,
                                       /*from_procedural_assertion=*/true,
                                       /*is_constant=*/true));
}

TEST(AttachSubroutineCall, LocalVarArgumentMustBeByValue) {
  // §16.11: if a local variable appears in an actual argument expression,
  // that argument shall be passed by value.
  EXPECT_FALSE(IsLocalVarArgPassingLegal(
      /*local_var_in_arg_expr=*/true, SubroutineArgPassing::kByRef));
  EXPECT_TRUE(IsLocalVarArgPassingLegal(
      /*local_var_in_arg_expr=*/true, SubroutineArgPassing::kByValueInput));
}

TEST(AttachSubroutineCall, RunsInReactiveRegionAndDoesNotBlockEval) {
  // §16.11: subroutines are scheduled in the Reactive region (like action
  // blocks) and assertion evaluation does not wait for them.
  EXPECT_EQ(AttachedSubroutineRegion(),
            AttachedSubroutineSchedulingRegion::kReactive);
  EXPECT_FALSE(AssertionEvalWaitsForAttachedSubroutine());
}

TEST(AttachSubroutineCall, RunsAtEveryEndPointInListOrder) {
  // §16.11: all attached calls execute at every end point of the sequence,
  // and within each end point the calls run in list order.
  EXPECT_TRUE(AttachedSubroutineRunsAtEveryEndPoint());
  EXPECT_TRUE(AttachedSubroutineCallsExecuteInListOrder());
}

TEST(AttachSubroutineCall, AllFiveCallableKindsAreAttachable) {
  // §16.11: the callable forms allowed for attachment are tasks, task
  // methods, void functions, void function methods, and system tasks.
  EXPECT_TRUE(IsAttachableSubroutineKind(AttachableSubroutineKind::kTask));
  EXPECT_TRUE(
      IsAttachableSubroutineKind(AttachableSubroutineKind::kTaskMethod));
  EXPECT_TRUE(
      IsAttachableSubroutineKind(AttachableSubroutineKind::kVoidFunction));
  EXPECT_TRUE(IsAttachableSubroutineKind(
      AttachableSubroutineKind::kVoidFunctionMethod));
  EXPECT_TRUE(
      IsAttachableSubroutineKind(AttachableSubroutineKind::kSystemTask));
}

TEST(AttachSubroutineCall, EachArgIsByValueOrByReference) {
  // §16.11: each argument of an attached subroutine call shall be passed
  // either by value (as an input) or by reference (ref / const ref). The
  // enumerated trio is the full set of legal passing modes.
  EXPECT_TRUE(
      IsArgPassingAllowedForAttachedCall(SubroutineArgPassing::kByValueInput));
  EXPECT_TRUE(IsArgPassingAllowedForAttachedCall(SubroutineArgPassing::kByRef));
  EXPECT_TRUE(
      IsArgPassingAllowedForAttachedCall(SubroutineArgPassing::kByConstRef));
}

TEST(AttachSubroutineCall, AutomaticAsNonConstantInputFromProceduralRejected) {
  // §16.11: an automatic variable shall not be passed as a non-constant
  // input from an attached subroutine call in procedural code. The
  // constant-input case is the only allowed mode for an automatic.
  EXPECT_FALSE(IsAutomaticArgUseAllowed(SubroutineArgPassing::kByValueInput,
                                        /*from_procedural_assertion=*/true,
                                        /*is_constant=*/false));
}

TEST(AttachSubroutineCall, AutomaticOutsideProceduralAssertionRejected) {
  // §16.11: the permission to pass an automatic variable as a constant
  // input is scoped to procedural-code subroutine calls. Outside that
  // scope, no automatic passing is allowed.
  EXPECT_FALSE(IsAutomaticArgUseAllowed(SubroutineArgPassing::kByValueInput,
                                        /*from_procedural_assertion=*/false,
                                        /*is_constant=*/true));
}

TEST(AttachSubroutineCall, ByValueInputTypeMustBeAllowedBy16_6) {
  // §16.11: a variable passed by value as an input shall be of a type
  // allowed in §16.6. The gate forwards the §16.6 verdict.
  EXPECT_TRUE(IsByValueInputArgumentTypeAllowed(/*type_allowed_in_16_6=*/true));
  EXPECT_FALSE(
      IsByValueInputArgumentTypeAllowed(/*type_allowed_in_16_6=*/false));
}

}  // namespace
