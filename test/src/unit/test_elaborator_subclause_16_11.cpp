#include <gtest/gtest.h>

#include "elaborator/sequence_degeneracy.h"
#include "elaborator/sequence_match_attach.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(AttachSubroutineCall, NoMatchSequenceRejectsAttachment) {
  // §16.11: the other degenerate class — a sequence that admits no match at
  // all — is likewise not a legal host for an attached sequence_match_item.
  EXPECT_FALSE(
      IsSequenceMatchItemAttachLegal(SequenceMatchClass::kAdmitsNoMatch));
}

TEST(AttachSubroutineCall, AutomaticByReferenceForbidden) {
  // §16.11: an automatic variable shall not be passed by reference under any
  // circumstance.
  EXPECT_FALSE(IsAutomaticArgUseAllowed(SubroutineArgPassing::kByRef,
                                        /*from_procedural_assertion=*/true,
                                        /*is_constant=*/true));
}

TEST(AttachSubroutineCall, AutomaticByConstReferenceForbidden) {
  // §16.11: the no-by-reference rule for automatics covers const ref just as
  // it covers ref — neither by-reference form is allowed for an automatic
  // variable, even a constant one from a procedural assertion.
  EXPECT_FALSE(IsAutomaticArgUseAllowed(SubroutineArgPassing::kByConstRef,
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

TEST(AttachSubroutineCall, LocalVarArgumentByConstReferenceRejected) {
  // §16.11: const ref is a by-reference form, so an actual argument that
  // mentions a local variable may not be passed by const ref either.
  EXPECT_FALSE(IsLocalVarArgPassingLegal(
      /*local_var_in_arg_expr=*/true, SubroutineArgPassing::kByConstRef));
}

TEST(AttachSubroutineCall, NonLocalVarArgumentAllowsAnyPassingMode) {
  // §16.11: the by-value restriction is scoped to arguments that mention a
  // local variable. When no local variable appears, any of the three passing
  // modes is permitted.
  EXPECT_TRUE(IsLocalVarArgPassingLegal(
      /*local_var_in_arg_expr=*/false, SubroutineArgPassing::kByRef));
  EXPECT_TRUE(IsLocalVarArgPassingLegal(
      /*local_var_in_arg_expr=*/false, SubroutineArgPassing::kByConstRef));
  EXPECT_TRUE(IsLocalVarArgPassingLegal(
      /*local_var_in_arg_expr=*/false, SubroutineArgPassing::kByValueInput));
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

TEST(AttachSubroutineCall, ByValueInputVariableTypeMustBeAllowed) {
  // §16.11: a variable passed by value as an input shall be of a type
  // allowed in §16.6. The gate forwards the §16.6 verdict.
  EXPECT_TRUE(IsByValueInputArgumentTypeAllowed(/*type_allowed_in_16_6=*/true));
  EXPECT_FALSE(
      IsByValueInputArgumentTypeAllowed(/*type_allowed_in_16_6=*/false));
}

// §16.11: an automatic variable is not passed by reference to a subroutine
// call attached to a sequence; by value, from an assertion in procedural
// code, it may be.
TEST(AttachedSubroutineCall, AnAutomaticPassedByReferenceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  task automatic show(ref int r);\n"
      "  endtask\n"
      "  task automatic shown(input int r);\n"
      "  endtask\n"
      "  always @(posedge clk) begin\n"
      "    automatic int k = 3;\n"
      "    a1: assert property ((a, show(k)) ##1 a);\n"
      "    a2: assert property ((a, shown(k)) ##1 a);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "an automatic variable may not be passed by reference";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 9, "16.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.11"));
}

// §16.11: an actual holding a local variable is passed by value, which the
// const ref formal of show does not.
TEST(AttachedSubroutineCall, ALocalPassedByReferenceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  task automatic show(const ref int r);\n"
      "  endtask\n"
      "  sequence s;\n"
      "    int v;\n"
      "    (a, v = 1, show(v)) ##1 a;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an actual holding a local variable shall be "
                            "passed by value",
                            7, "16.11"));
}

// §16.11: a variable passed by value is of a type §16.6 allows, which
// chandle is not.
TEST(AttachedSubroutineCall, AChandlePassedByValueIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  chandle h;\n"
      "  function void show(input chandle c);\n"
      "  endfunction\n"
      "  sequence s;\n"
      "    @(posedge clk) (a, show(h)) ##1 a;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a variable passed by value shall be of a type an "
                            "assertion may use",
                            7, "16.11"));
}

}  // namespace
