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

}  // namespace
