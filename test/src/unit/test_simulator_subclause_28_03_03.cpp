#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(GateDelaySimulator, ProductionUndecoratedGateLeavesSchedulerAtInputTime) {
  // A gate declared without a delay specification keeps the production
  // scheduler at the time of the last input change: the coroutine takes the
  // no-delay branch and adds no further events.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and g(y, a, a);\n"
      "  initial begin a = 1'b0; #4 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 4u);
}

TEST(GateDelaySimulator, GateWithDelaySpecifiesPropagationDelay) {
  // §28.3.3: a delay specification specifies the propagation delay through the
  // gate -- the positive counterpart to the no-delay case above. The input
  // changes at t=4; with a #3 delay the resulting output transition is
  // scheduled three ticks later, so the last event the production scheduler
  // processes lands at t=7. The delay is applied, not dropped.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #3 g(y, a, a);\n"
      "  initial begin a = 1'b0; #4 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 7u);
}

}  // namespace
