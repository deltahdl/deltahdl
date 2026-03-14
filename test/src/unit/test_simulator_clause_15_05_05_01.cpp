#include "fixture_simulator.h"
#include "simulator/lowerer.h"

namespace {

// §15.5.5.1: After merge (a = b), triggering a unblocks waiter on b.
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

// §15.5.5.1: After merge (a = b), triggering b unblocks waiter on a.
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

// §15.5.5.1: Chained merge (a=c; b=a) propagates trigger to all aliases.
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

// §15.5.5.1: Process blocked on @E2 before E2=E1 never unblocks.
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

// §15.5.5.1: Triggered state propagates across merged events.
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

}  // namespace
