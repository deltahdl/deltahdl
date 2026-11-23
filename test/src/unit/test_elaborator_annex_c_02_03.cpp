#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

::testing::AssertionResult ReportedEnded(const ElabFixture& f,
                                         std::string_view seq, uint32_t line) {
  return ReportedError(
      f.diag.Diagnostics(),
      "the ended sequence method has been removed; use the "
      "triggered method to detect the end point of sequence '" +
          std::string(seq) + "'",
      line, "C.2.3");
}

TEST(EndedSequenceMethodElaboration, ReadInAFunctionNeverCalledIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  function automatic logic f();\n"
      "    return s.ended;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 7));
}

TEST(EndedSequenceMethodElaboration, ReadInABranchNeverTakenIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a, r;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial if (1'b0) r = s.ended;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
}

TEST(EndedSequenceMethodElaboration, ReadInASequenceExpressionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  assert property (@(posedge clk) b ##1 s.ended);\n"
      "  sequence s2;\n"
      "    @(posedge clk) b ##1 s.ended;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
  EXPECT_TRUE(ReportedEnded(f, "s", 8));
}

TEST(EndedSequenceMethodElaboration, ReadInAContinuousAssignmentIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a;\n"
      "  wire w;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  assign w = s.ended;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 7));
}

TEST(EndedSequenceMethodElaboration, TriggeredIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b, r;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial r = s.triggered;\n"
      "  assert property (@(posedge clk) b ##1 s.triggered);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(std::ranges::none_of(
      f.diag.Diagnostics(),
      [](const Diagnostic& d) { return d.subclause == "C.2.3"; }));
}

TEST(EndedSequenceMethodElaboration, ReadInAnInterfaceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n"
      "  logic clk, a, r;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial r = s.ended;\n"
      "endinterface\n"
      "module t;\n"
      "  ifc i ();\n"
      "endmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
}

TEST(EndedSequenceMethodElaboration, ReadInAProgramIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  logic clk, a, r;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial r = s.ended;\n"
      "endprogram\n",
      f, "p");
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
}

TEST(EndedSequenceMethodElaboration, ReadInACheckerAlwaysFfIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk, input logic a);\n"
      "  logic r;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  always_ff @(posedge clk) r <= s.ended;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
}

TEST(EndedSequenceMethodElaboration, ReadInAPropertyDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  property p;\n"
      "    @(posedge clk) b |-> s.ended;\n"
      "  endproperty\n"
      "  assert property (p);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 7));
}

TEST(EndedSequenceMethodElaboration, ReadInACoverSequenceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  cover sequence (@(posedge clk) b ##1 s.ended);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
}

TEST(EndedSequenceMethodElaboration, ReadInAWaitConditionIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial wait (s.ended);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
}

TEST(EndedSequenceMethodElaboration, ReadOnASequenceInstanceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a, r;\n"
      "  sequence s(x);\n"
      "    @(posedge clk) x;\n"
      "  endsequence\n"
      "  initial r = s(a).ended;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
}

TEST(EndedSequenceMethodElaboration, ReadWrittenAsACallIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a, r;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial r = s.ended();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
}

TEST(EndedSequenceMethodElaboration, DISABLED_ReadInAGenerateBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a, r;\n"
      "  if (1) begin : g\n"
      "    sequence s;\n"
      "      @(posedge clk) a;\n"
      "    endsequence\n"
      "    initial r = s.ended;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 7));
}

TEST(EndedSequenceMethodElaboration,
     DISABLED_ReadThroughAPackageScopeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  logic clk, a;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endpackage\n"
      "module t;\n"
      "  logic r;\n"
      "  initial r = pk::s.ended;\n"
      "endmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedEnded(f, "s", 9));
}

TEST(EndedSequenceMethodElaboration,
     DISABLED_ReadThroughAnInterfaceInstanceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n"
      "  logic clk, a;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endinterface\n"
      "module t;\n"
      "  logic r;\n"
      "  ifc ii ();\n"
      "  initial r = ii.s.ended;\n"
      "endmodule\n",
      f, "t");
  EXPECT_TRUE(ReportedEnded(f, "s", 10));
}

TEST(EndedSequenceMethodElaboration, DISABLED_ReadAsAnEventControlIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial @(s.ended);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedEnded(f, "s", 6));
}

TEST(EndedSequenceMethodElaboration,
     TriggeredInAGenerateBlockAndAsAnEventControlIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic clk, a, r;\n"
      "  sequence s;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  initial @(s.triggered);\n"
      "  if (1) begin : g\n"
      "    sequence sg;\n"
      "      @(posedge clk) a;\n"
      "    endsequence\n"
      "    initial r = sg.triggered;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(std::ranges::none_of(
      f.diag.Diagnostics(),
      [](const Diagnostic& d) { return d.subclause == "C.2.3"; }));
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
