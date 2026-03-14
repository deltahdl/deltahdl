#include <gtest/gtest.h>

#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"

namespace {

TEST(IpcSync, WaitOrderInOrderExecutesThenBranch) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b) result = 42;\n"
      "    else result = 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 -> b;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IpcSync, WaitOrderOutOfOrderExecutesElseBranch) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b) result = 42;\n"
      "    else result = 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> b;\n"
      "    #1 -> a;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IpcSync, WaitOrderThreeEventsInOrder) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b, c;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 -> b;\n"
      "    #1 -> c;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, WaitOrderThreeEventsOutOfOrder) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b, c;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) result = 1;\n"
      "    else result = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 -> c;\n"
      "    #1 -> b;\n"
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

TEST(IpcSync, WaitOrderNullActionSuccess) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [7:0] after;\n"
      "  initial begin\n"
      "    wait_order(a, b);\n"
      "    after = 8'd1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 -> b;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("after");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(IpcSync, WaitOrderFirstEventAlreadyTriggered) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    -> a;\n"
      "    wait_order(a, b) result = 42;\n"
      "    else result = 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> b;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(IpcSync, WaitOrderEmptyEventsCompletes) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait_order(a);\n"
      "    x = 8'd5;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> a;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(IpcSync, WaitOrderElseOnlyBranch) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    wait_order(a, b)\n"
      "    else result = 77;\n"
      "    #2 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> b;\n"
      "    #1 -> a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}  // namespace
