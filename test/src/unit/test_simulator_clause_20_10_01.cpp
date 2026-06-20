#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §20.10.1 — when a $fatal elaboration severity task survives elaboration,
// the simulator shall refuse to start. Lowering must not register variables
// or processes from a blocked design.
TEST(ElabSeverityTaskSim, FatalBlocksLowering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd5;\n"
      "  $fatal(1, \"abort\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_TRUE(design->simulation_blocked);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("x"), nullptr);
}

// §20.10.1 — $warning at elaboration shall not prevent simulation from
// starting. Lowering must proceed and the initial-block assignment must
// take effect.
TEST(ElabSeverityTaskSim, WarningDoesNotBlockLowering) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd9;\n"
      "  $warning(\"careful\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->simulation_blocked);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

}  // namespace
