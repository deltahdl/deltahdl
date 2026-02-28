// §9.2.3: Final procedures

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, FinalBlockExecutesAfterRun) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  final x = 77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // Before RunFinalBlocks, x should still have default value.
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);

  f.ctx.RunFinalBlocks();
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(Lowerer, FinalBlockNotScheduledAtTimeZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 10;\n"
      "  final x = 77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  // After scheduler, initial ran (x=10) but final didn't.
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(Lowerer, FinalBlocksFIFOOrder) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  final x = 10;\n"
      "  final x = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Second final block overwrites first, so x == 20.
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

}  // namespace
