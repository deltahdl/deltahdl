#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Annex C.2.3: the ended sequence method.
//
// IEEE 1800-2005 required the ended method to detect a sequence end point
// within a sequence expression, while triggered detected the same end point in
// other contexts. Because the two had identical meaning under mutually
// exclusive usage rules, IEEE 1800-2023 removed ended and lets triggered serve
// both roles. A surviving reference to the ended method on a named sequence is
// the removed construct and must be reported when the simulator evaluates it,
// while the retained triggered method must still evaluate without complaint.

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
// no longer exists; evaluating it is rejected.
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
// deprecated construct and is left alone by this rule.
TEST(EndedSequenceMethodDeprecated, EndedOnNonSequenceIsNotRejectedByThisRule) {
  EXPECT_FALSE(
      RunReportsError("module t;\n"
                      "  logic [7:0] s;\n"
                      "  logic r;\n"
                      "  initial r = s.ended;\n"
                      "endmodule\n"));
}

}  // namespace
