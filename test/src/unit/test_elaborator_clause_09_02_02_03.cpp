// §9.2.2.3: Latched logic always_latch procedure

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// §9.2.3: always_latch executes at time 0
// The always_latch procedure executes once automatically at time 0.
// =============================================================================
// 1. always_latch body executes at time 0 with default variable values.
TEST(SimCh9c, ExecutesAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // en defaults to 0, so q should retain its default value of 0.
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 8u);
  EXPECT_EQ(q->value.ToUint64(), 0u);
}

// 2. always_latch with unconditional assignment sets output at time 0.
TEST(SimCh9c, UnconditionalAssignAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  always_latch\n"
      "    q = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xABu);
}

}  // namespace
