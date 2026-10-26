#include <gtest/gtest.h>

#include <algorithm>
#include <string>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// Annex C.2.3: the ended sequence method.
//
// IEEE 1800-2005 required the ended method to detect a sequence end point
// within a sequence expression, while triggered detected the same end point in
// other contexts. Because the two had identical meaning under mutually
// exclusive usage rules, IEEE 1800-2023 removed ended and lets triggered serve
// both roles. A surviving reference to the ended method on a named sequence is
// the removed construct, and a design holding one is rejected. Elaboration
// reports it, ahead of any run; test_elaborator_annex_c_02_03.cpp covers it in
// code no run reaches. The retained triggered method still evaluates without
// complaint.

// Helper: elaborate and lower a design, run it, and report whether the run
// produced any diagnostics.
bool RunReportsError(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  if (!design) return f.diag.HasErrors();
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.diag.HasErrors();
}

// Reading the deprecated ended method off a named sequence names a method that
// no longer exists; a design that does so is rejected.
TEST(EndedSequenceMethodDeprecated, EndedMethodOnSequenceIsRejected) {
  EXPECT_TRUE(
      RunReportsError("module t;\n"
                      "  logic clk, a;\n"
                      "  logic r;\n"
                      "  sequence s;\n"
                      "    @(posedge clk) a;\n"
                      "  endsequence\n"
                      "  initial r = s.ended;\n"
                      "endmodule\n"));
}

// triggered replaces ended and remains a defined sequence method, so reading it
// off the same named sequence evaluates cleanly.
TEST(EndedSequenceMethodDeprecated, TriggeredMethodOnSequenceStillEvaluates) {
  EXPECT_FALSE(
      RunReportsError("module t;\n"
                      "  logic clk, a;\n"
                      "  logic r;\n"
                      "  sequence s;\n"
                      "    @(posedge clk) a;\n"
                      "  endsequence\n"
                      "  initial r = s.triggered;\n"
                      "endmodule\n"));
}

// The removal targets the sequence method specifically. A member named ended
// whose base is an ordinary variable rather than a named sequence is not the
// deprecated construct and is left alone by this rule; §23.7 a) is what
// refuses it, a select through an integral variable naming nothing.
TEST(EndedSequenceMethodDeprecated, EndedOnNonSequenceIsNotRejectedByThisRule) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [7:0] s;\n"
      "  logic r;\n"
      "  initial r = s.ended;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(std::ranges::none_of(
      f.diag.Diagnostics(),
      [](const Diagnostic& d) { return d.subclause == "C.2.3"; }));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "is not a built-in method", 4,
                            "23.7"));
}

// Annex C.2.3: the usage of the ended sequence method is deprecated and does
// not appear in this version of the standard, with triggered allowed in its
// place. The report that rejects a use of ended names C.2.3.
TEST(EndedSequenceMethodDeprecated, RejectionNamesC_2_3) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, b;\n"
      "  logic v;\n"
      "  sequence sq;\n"
      "    @(posedge clk) b;\n"
      "  endsequence\n"
      "  initial v = sq.ended;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ended sequence method has been removed", 7,
                            "C.2.3"));
}

}  // namespace
