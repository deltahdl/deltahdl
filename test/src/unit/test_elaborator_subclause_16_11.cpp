#include <gtest/gtest.h>

#include <cstdint>

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
  // either by value (as an input) or by reference (ref / const ref). An
  // output or inout formal copies its argument back (§13.5), which is
  // neither.
  EXPECT_TRUE(
      IsArgPassingAllowedForAttachedCall(SubroutineArgPassing::kByValueInput));
  EXPECT_TRUE(IsArgPassingAllowedForAttachedCall(SubroutineArgPassing::kByRef));
  EXPECT_TRUE(
      IsArgPassingAllowedForAttachedCall(SubroutineArgPassing::kByConstRef));
  EXPECT_FALSE(
      IsArgPassingAllowedForAttachedCall(SubroutineArgPassing::kCopiedOut));
  EXPECT_FALSE(
      IsArgPassingAllowedForAttachedCall(SubroutineArgPassing::kCopiedInOut));
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

// §16.11: a subroutine call is not attached to a sequence that admits an
// empty match, as b[*0:1] does.
TEST(AttachedSubroutineCall, ACallOnAnEmptyMatchingSequenceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b, c;\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 (b[*0:1], $display(\"hit\")) ##1 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a subroutine call may not be attached to a "
                            "sequence that admits an empty match",
                            4, "16.11"));
}

// §16.11: an argument of a call attached to a sequence is passed by value
// as an input or by reference; an output or an inout formal copies it back
// (§13.5) instead, which is neither way.
TEST(AttachedSubroutineCall, AnArgumentToAnOutputOrInoutFormalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  int count;\n"
      "  task tick(output int v); v = 1; endtask\n"
      "  task bump(inout int v); v++; endtask\n"
      "  task show(input int v); endtask\n"
      "  sequence s1; @(posedge clk) (a, tick(count)) ##1 a; endsequence\n"
      "  sequence s2; @(posedge clk) (a, bump(count)) ##1 a; endsequence\n"
      "  sequence s3; @(posedge clk) (a, show(count)) ##1 a; endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "an actual shall be passed by value as an input or by reference";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 8, "16.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 9, "16.11"));
}

// §16.11 with §23.9, §26.3, §8.10, §8.13 and §8.5: the rules on an attached
// call's actuals reach a subroutine written through a package's scope, one a
// wildcard or an explicit package import makes visible, one the compilation
// unit declares, a class's static method written through the class's scope,
// and a method called through a handle, its own class's or one it inherits;
// each passes the local variable v by reference here. A call of a task through
// an instance's name, and of a sequence's formal argument, which stands for
// its actual, pass nothing by reference and draw no report.
TEST(AttachedSubroutineCall, ACalleeReachedThroughAScopeOrAHandleIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "package P;\n"
      "  task automatic note(ref int v); endtask\n"
      "endpackage\n"
      "package Q;\n"
      "  task automatic stamp(ref int v); endtask\n"
      "endpackage\n"
      "task automatic logit(ref int v); endtask\n"
      "module sub;\n"
      "  task show(input int v); endtask\n"
      "endmodule\n"
      "module m;\n"
      "  import P::*;\n"
      "  import Q::stamp;\n"
      "  bit clk, a;\n"
      "  class C;\n"
      "    int p;\n"
      "    static task mark(ref int v); endtask\n"
      "    task poke(ref int v); endtask\n"
      "  endclass\n"
      "  class D extends C;\n"
      "  endclass\n"
      "  C h = new;\n"
      "  D k = new;\n"
      "  sub u();\n"
      "  sequence s1; int v; @(posedge clk) (a, v = 1, P::note(v)); "
      "endsequence\n"
      "  sequence s2; int v; @(posedge clk) (a, v = 1, note(v)); "
      "endsequence\n"
      "  sequence s3; int v; @(posedge clk) (a, v = 1, stamp(v)); "
      "endsequence\n"
      "  sequence s4; int v; @(posedge clk) (a, v = 1, logit(v)); "
      "endsequence\n"
      "  sequence s5; int v; @(posedge clk) (a, v = 1, C::mark(v)); "
      "endsequence\n"
      "  sequence s6; int v; @(posedge clk) (a, v = 1, h.poke(v)); "
      "endsequence\n"
      "  sequence s7; int v; @(posedge clk) (a, v = 1, k.poke(v)); "
      "endsequence\n"
      "  sequence s8; int v; @(posedge clk) (a, v = 1, u.show(v)); "
      "endsequence\n"
      "  sequence s9(q); @(posedge clk) (a, q); endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "an actual holding a local variable shall be passed by value";
  for (uint32_t line = 25; line <= 31; ++line) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, line, "16.11"))
        << "line " << line;
  }
  for (uint32_t line : {32u, 33u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "", line, "16.11"))
        << "line " << line;
  }
}

// §16.11 with §35.5: a subroutine the module imports through DPI is a
// subroutine an attached call may call, and its actuals are held to the
// same rules: chandle is no type an assertion may use (§16.6).
TEST(AttachedSubroutineCall, AnImportedDpiCalleeIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  chandle h;\n"
      "  import \"DPI-C\" function void show(input chandle c);\n"
      "  sequence s; @(posedge clk) (a, show(h)) ##1 a; endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a variable passed by value shall be of a type an "
                            "assertion may use",
                            5, "16.11"));
}

}  // namespace
