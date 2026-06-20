#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, WhileBasic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    while (x > 0) x = x - 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(LoopStatementSim, WhileZeroIter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    while (0) x = 8'd99;\n"
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

TEST(LoopStatementSim, WhileBreak) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    while (1) begin\n"
      "      if (x == 8'd5) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
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

TEST(LoopStatementSim, WhileContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, sum;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    sum = 8'd0;\n"
      "    while (x < 8'd5) begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) continue;\n"
      "      sum = sum + x;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(LoopStatementSim, WhileBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, cnt;\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    cnt = 8'd0;\n"
      "    while (x > 0) begin\n"
      "      x = x - 8'd1;\n"
      "      cnt = cnt + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, WhileXConditionNoIteration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic cond;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    cond = 1'bx;\n"
      "    while (cond) x = 8'd0;\n"
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

// §12.7.4: a control expression that is not true at entry shall skip the body
// entirely. A high-impedance value is not true (truth per §12.4), so the
// pre-test gate in ExecWhile breaks before the first iteration. Edge-case
// sibling of WhileXConditionNoIteration covering the Z case.
TEST(LoopStatementSim, WhileZConditionNoIteration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic cond;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    cond = 1'bz;\n"
      "    while (cond) x = 8'd0;\n"
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

// §12.7.4: the body repeats as long as the control expression is true. A bare
// multibit condition is true while any bit is set and false once the value is
// zero, so the loop iterates until the register drains to zero. Mirrors the
// count-ones example in the subclause and exercises truthiness of a wide
// (non-relational) condition through ExecWhile.
TEST(LoopStatementSim, WhileVectorConditionIteratesUntilZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] tempreg;\n"
      "  logic [7:0] count;\n"
      "  initial begin\n"
      "    count = 8'd0;\n"
      "    tempreg = 8'b1011_0010;\n"
      "    while (tempreg) begin\n"
      "      if (tempreg[0]) count = count + 8'd1;\n"
      "      tempreg = tempreg >> 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(count->value.ToUint64(), 4u);  // 1011_0010 holds four set bits
  auto* tempreg = f.ctx.FindVariable("tempreg");
  ASSERT_NE(tempreg, nullptr);
  EXPECT_EQ(tempreg->value.ToUint64(), 0u);  // ran until the register hit zero
}

}  // namespace
