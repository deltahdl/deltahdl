#include "fixture_simulator.h"
#include "simulator/lowerer.h"

namespace {

TEST(IpcSync, MergedTriggerUnblocksAliasWaiter) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    fork\n"
      "      begin @b; result = 10; end\n"
      "      begin #1 -> a; end\n"
      "    join\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(IpcSync, MergedTriggerUnblocksOriginalWaiter) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    fork\n"
      "      begin @a; result = 20; end\n"
      "      begin #1 -> b; end\n"
      "    join\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(IpcSync, ChainedMergePropagatesTrigger) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b, c;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = c;\n"
      "    b = a;\n"
      "    fork\n"
      "      begin @b; result = 30; end\n"
      "      begin #1 -> c; end\n"
      "    join\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(IpcSync, ProcessBlockedBeforeMergeDoesNotUnblock) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event E1, E2;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    fork\n"
      "      begin @E2; result = 1; end\n"
      "      begin E2 = E1; -> E2; end\n"
      "    join_any\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// A single trigger on one merged name must reach processes waiting on every
// other name merged into the same synchronization object, not just one. This
// observes the watcher list of the shared Variable being drained for multiple
// distinct alias names (the "also triggers a and b" multi-target case).
TEST(IpcSync, MergedTriggerWakesAllAliasWaiters) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b, c;\n"
      "  logic [31:0] r1, r2;\n"
      "  initial begin\n"
      "    r1 = 0; r2 = 0;\n"
      "    a = c;\n"
      "    b = a;\n"
      "    fork\n"
      "      begin @a; r1 = 1; end\n"
      "      begin @b; r2 = 1; end\n"
      "      begin #1 -> c; end\n"
      "    join\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r1 = f.ctx.FindVariable("r1");
  auto* r2 = f.ctx.FindVariable("r2");
  ASSERT_NE(r1, nullptr);
  ASSERT_NE(r2, nullptr);
  EXPECT_EQ(r1->value.ToUint64(), 1u);
  EXPECT_EQ(r2->value.ToUint64(), 1u);
}

TEST(IpcSync, MergedEventTriggeredStateShared) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    -> a;\n"
      "    wait(b.triggered);\n"
      "    result = 55;\n"
      "  end\n"
      "  initial #1 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

}
