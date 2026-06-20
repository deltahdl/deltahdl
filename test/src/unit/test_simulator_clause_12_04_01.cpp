#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ConditionalStatementSim, IfElseIfChainSelectsCorrectBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd2;\n"
      "    if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else if (a == 8'd2) x = 8'd30;\n"
      "    else x = 8'd40;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(ConditionalStatementSim, DeepIfElseIfLastElseTaken) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (0) x = 8'd1;\n"
      "    else if (0) x = 8'd2;\n"
      "    else if (0) x = 8'd3;\n"
      "    else x = 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(ConditionalStatementSim, IfElseIfFirstConditionTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(ConditionalStatementSim, IfElseIfBlockBodyFirstMatchTerminatesChain) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      x = 8'd11;\n"
      "      y = 8'd22;\n"
      "    end else if (1) begin\n"
      "      x = 8'd33;\n"
      "      y = 8'd44;\n"
      "    end else begin\n"
      "      x = 8'd55;\n"
      "      y = 8'd66;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  auto* yv = f.ctx.FindVariable("y");
  ASSERT_NE(xv, nullptr);
  ASSERT_NE(yv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 11u);
  EXPECT_EQ(yv->value.ToUint64(), 22u);
}

TEST(ConditionalStatementSim, IfElseIfBlockBodyDefaultElseExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd0; y = 8'd0;\n"
      "    if (0) begin x = 8'd1; y = 8'd2; end\n"
      "    else if (0) begin x = 8'd3; y = 8'd4; end\n"
      "    else begin x = 8'd55; y = 8'd66; end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* xv = f.ctx.FindVariable("x");
  auto* yv = f.ctx.FindVariable("y");
  ASSERT_NE(xv, nullptr);
  ASSERT_NE(yv, nullptr);
  EXPECT_EQ(xv->value.ToUint64(), 55u);
  EXPECT_EQ(yv->value.ToUint64(), 66u);
}

TEST(ConditionalStatementSim, IfElseIfNoMatchNoElseRetainsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd77;\n"
      "    if (0) x = 8'd10;\n"
      "    else if (0) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}  // namespace
