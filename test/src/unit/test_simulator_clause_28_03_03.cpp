#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(GateDelaySimulator, AbsentDelaySpecYieldsZeroPropagation) {
  // When a gate or switch is declared without a delay specification, the
  // pipeline funnels zero-valued rise and fall slots into the delay helper
  // and the helper short-circuits to zero for every from-to transition.
  static constexpr Val4 kVals[] = {Val4::kV0, Val4::kV1, Val4::kX, Val4::kZ};
  for (Val4 from : kVals) {
    for (Val4 to : kVals) {
      EXPECT_EQ(ComputeGateDelay(0, 0, from, to), 0u);
    }
  }
}

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

}  // namespace
