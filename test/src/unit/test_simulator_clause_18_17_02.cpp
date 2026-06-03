#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// 18.17.2: when the if-else condition is false, the production following the
// optional else is generated.
TEST(RandsequenceSim, IfElseProductionFalseSelectsElse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : if (0) a else b;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// 18.17.2: when the if-else condition is true, the production following the
// expression is generated (and the else production is not).
TEST(RandsequenceSim, IfElseProductionTrueSelectsThen) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : if (1) a else b;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// 18.17.2: the else branch is optional. With no else and a false condition,
// neither the then production nor any else production is generated, so the
// surrounding state is left untouched.
TEST(RandsequenceSim, IfWithoutElseFalseGeneratesNothing) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    randsequence(main)\n"
      "      main : if (0) a;\n"
      "      a : { x = 8'd1; };\n"
      "    endsequence\n"
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

// 18.17.2: the condition is treated as a Boolean. Any non-zero value is true,
// not just literal 1, so a condition of 5 still selects the then production.
TEST(RandsequenceSim, NonOneTruthyConditionSelectsThen) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : if (5) a else b;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// 18.17.2: the condition can be any expression, not just a constant. A
// comparison over a runtime variable drives the branch selection; here n is 3
// so n < 2 is false and the else production is generated.
TEST(RandsequenceSim, ConditionFromExpressionSelectsBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    n = 8'd3;\n"
      "    randsequence(main)\n"
      "      main : if (n < 2) a else b;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}
