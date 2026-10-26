#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

// Annex C.2.3: the ended sequence method.
//
// IEEE 1800-2005 had a sequence's end point read with ended inside a sequence
// expression and with triggered elsewhere. This version removes ended and lets
// triggered serve in both places, so a read of ended off a named sequence names
// a method the language no longer has. That is a property of the source text,
// so elaboration reports it wherever it is written, whether or not a run would
// ever evaluate it. test_simulator_annex_c_02_03.cpp observes the same report
// through a run.

namespace {

// Whether the C.2.3 report on a read of ended off the sequence `seq` stands at
// `line`.
::testing::AssertionResult ReportedEnded(const ElabFixture& f,
                                         std::string_view seq, uint32_t line) {
  return ReportedError(
      f.diag.Diagnostics(),
      "the ended sequence method has been removed; use the "
      "triggered method to detect the end point of sequence '" +
          std::string(seq) + "'",
      line, "C.2.3");
}

// A function no process ever calls still holds the read in its body.
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

// A branch whose condition is constant false is never taken by a run, and
// the read in it is reported all the same.
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

// A sequence expression is where IEEE 1800-2005 had ended written, both in a
// concurrent assertion's property and in another sequence's declaration.
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

// A continuous assignment stands outside every procedure and is checked as
// well.
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

// triggered, which takes ended's place, draws no C.2.3 report in either a
// procedure or a sequence expression.
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
