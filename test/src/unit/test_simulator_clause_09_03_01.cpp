#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SequentialBlockSimulation, SeqBlockExecutionOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(SequentialBlockSimulation, SeqBlockValuePropagation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    b = a + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(SequentialBlockSimulation, SeqBlockSequentialExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 10;\n"
      "      b = 20;\n"
      "      c = a + b;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 30u);
}

TEST(SequentialBlockSimulation, EmptySeqBlockNoOp) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    begin\n"
      "    end\n"
      "    x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(SequentialBlockSimulation, RelativeDelaySemantics) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    #5 x = 8'd1;\n"
      "    #5 y = 8'd2;\n"
      "  end\n"
      "  logic [7:0] snap_x;\n"
      "  initial begin\n"
      "    #7 snap_x = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* snap = f.ctx.FindVariable("snap_x");
  ASSERT_NE(snap, nullptr);
  EXPECT_EQ(snap->value.ToUint64(), 1u);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 2u);
}

TEST(SequentialBlockSimulation, BlockLocalVarDecl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    int tmp;\n"
      "    tmp = 42;\n"
      "    result = tmp[7:0];\n"
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

}  // namespace
