#include <gtest/gtest.h>

#include <algorithm>
#include <string>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

bool RunReportsError(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  if (!design) return f.diag.HasErrors();
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.diag.HasErrors();
}

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
