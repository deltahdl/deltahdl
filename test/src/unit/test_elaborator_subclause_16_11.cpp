#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/sequence_degeneracy.h"
#include "elaborator/sequence_match_attach.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AttachSubroutineCall, EmptyMatchSequenceRejectsAttachment) {
  EXPECT_FALSE(
      IsSequenceMatchItemAttachLegal(SequenceMatchClass::kAdmitsOnlyEmpty));
}

TEST(AttachSubroutineCall, NondegenerateSequenceAcceptsAttachment) {
  EXPECT_TRUE(IsSequenceMatchItemAttachLegal(
      SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

TEST(AttachSubroutineCall, NoMatchSequenceRejectsAttachment) {
  EXPECT_FALSE(
      IsSequenceMatchItemAttachLegal(SequenceMatchClass::kAdmitsNoMatch));
}

TEST(AttachSubroutineCall, AutomaticByReferenceForbidden) {
  EXPECT_FALSE(
      IsAutomaticArgUseAllowed(SubroutineArgPassing::kByRef, true, true));
}

TEST(AttachSubroutineCall, AutomaticByConstReferenceForbidden) {
  EXPECT_FALSE(
      IsAutomaticArgUseAllowed(SubroutineArgPassing::kByConstRef, true, true));
}

TEST(AttachSubroutineCall, AutomaticAsConstantInputFromProceduralAllowed) {
  EXPECT_TRUE(IsAutomaticArgUseAllowed(SubroutineArgPassing::kByValueInput,
                                       true, true));
}

TEST(AttachSubroutineCall, LocalVarArgumentMustBeByValue) {
  EXPECT_FALSE(IsLocalVarArgPassingLegal(true, SubroutineArgPassing::kByRef));
  EXPECT_TRUE(
      IsLocalVarArgPassingLegal(true, SubroutineArgPassing::kByValueInput));
}

TEST(AttachSubroutineCall, LocalVarArgumentByConstReferenceRejected) {
  EXPECT_FALSE(
      IsLocalVarArgPassingLegal(true, SubroutineArgPassing::kByConstRef));
}

TEST(AttachSubroutineCall, NonLocalVarArgumentAllowsAnyPassingMode) {
  EXPECT_TRUE(IsLocalVarArgPassingLegal(false, SubroutineArgPassing::kByRef));
  EXPECT_TRUE(
      IsLocalVarArgPassingLegal(false, SubroutineArgPassing::kByConstRef));
  EXPECT_TRUE(
      IsLocalVarArgPassingLegal(false, SubroutineArgPassing::kByValueInput));
}

TEST(AttachSubroutineCall, RunsAtEveryEndPointInListOrder) {
  EXPECT_TRUE(AttachedSubroutineRunsAtEveryEndPoint());
  EXPECT_TRUE(AttachedSubroutineCallsExecuteInListOrder());
}

TEST(AttachSubroutineCall, AllFiveCallableKindsAreAttachable) {
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
  EXPECT_FALSE(IsAutomaticArgUseAllowed(SubroutineArgPassing::kByValueInput,
                                        true, false));
}

TEST(AttachSubroutineCall, AutomaticOutsideProceduralAssertionRejected) {
  EXPECT_FALSE(IsAutomaticArgUseAllowed(SubroutineArgPassing::kByValueInput,
                                        false, true));
}

TEST(AttachSubroutineCall, ByValueInputVariableTypeMustBeAllowed) {
  EXPECT_TRUE(IsByValueInputArgumentTypeAllowed(true));
  EXPECT_FALSE(IsByValueInputArgumentTypeAllowed(false));
}

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
      "  bit clk, a; int q[$];\n"
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
      "  sequence s9(r); @(posedge clk) (a, r); endsequence\n"
      "  sequence s10; @(posedge clk) (a, q.push_back(1)); endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "an actual holding a local variable shall be passed by value";
  for (uint32_t line = 25; line <= 31; ++line) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, line, "16.11"))
        << "line " << line;
  }
  for (uint32_t line : {32u, 33u, 34u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "", line, "16.11"))
        << "line " << line;
  }
}

TEST(AttachedSubroutineCall, ACalleeReachedThroughAnInstanceIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  task automatic tick(ref int v); endtask\n"
      "endmodule\n"
      "module mid;\n"
      "  sub w();\n"
      "endmodule\n"
      "interface bus;\n"
      "  task automatic tick(ref int v); endtask\n"
      "endinterface\n"
      "module m;\n"
      "  bit clk, a;\n"
      "  sub u();\n"
      "  mid n();\n"
      "  bus i();\n"
      "  sequence s1; int v; @(posedge clk) (a, v = 1, u.tick(v)); "
      "endsequence\n"
      "  sequence s2; int v; @(posedge clk) (a, v = 1, n.w.tick(v)); "
      "endsequence\n"
      "  sequence s3; int v; @(posedge clk) (a, v = 1, i.tick(v)); "
      "endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "an actual holding a local variable shall be passed by value";
  for (uint32_t line = 15; line <= 17; ++line) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, line, "16.11"))
        << "line " << line;
  }
}

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

TEST(AttachedTaskElaboration, ADpiImportedTaskIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "import \"DPI-C\" task dt(input int v);\n"
      "module m;\n"
      "  logic clk, a, b;\n"
      "  int k;\n"
      "  import \"DPI-C\" task dm(input int v);\n"
      "  c1: cover property (@(posedge clk) (a ##1 b, dt(k), dm(k)));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
