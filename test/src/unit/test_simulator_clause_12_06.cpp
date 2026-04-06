

#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Matches, ExactMatchTrue) {
  SimFixture f;
  auto* expr = ParseExprFrom("42 matches 42", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kBinary);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, ExactMatchFalse) {
  SimFixture f;
  auto* expr = ParseExprFrom("42 matches 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, VariableMatch) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("sig", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  auto* expr = ParseExprFrom("sig matches 8'hAB", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, WildcardXInPattern) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("wv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = ParseExprFrom("wv matches 4'b1x1x", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, WildcardZInPattern) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("zv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = ParseExprFrom("zv matches 4'b1?0?", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, WildcardPatternMismatch) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("mm", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b0010);

  auto* expr = ParseExprFrom("mm matches 4'b1x1x", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, ResultAlwaysDetermined) {
  SimFixture f;
  MakeVar4(f, "xv", 4, 0b0000, 0b1111);
  auto* expr = ParseExprFrom("xv matches 4'b0000", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
}

TEST(Matches, CaseMatchesWildcardPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    case(sel) matches\n"
      "      4'b0???: x = 8'd1;\n"
      "      4'b1???: x = 8'd2;\n"
      "      default: x = 8'd0;\n"
      "    endcase\n"
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

TEST(Matches, CaseMatchesWildcardNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] sel;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sel = 4'b1010;\n"
      "    case(sel) matches\n"
      "      4'b0??0: x = 8'd1;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(Matches, TripleAmpTrue) {
  SimFixture f;
  auto* expr = ParseExprFrom("1 &&& 1", f);
  ASSERT_NE(expr, nullptr);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Matches, TripleAmpFalseShortCircuit) {
  SimFixture f;
  auto* expr = ParseExprFrom("0 &&& 1", f);
  ASSERT_NE(expr, nullptr);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(Matches, TripleAmpSecondFalse) {
  SimFixture f;
  auto* expr = ParseExprFrom("1 &&& 0", f);
  ASSERT_NE(expr, nullptr);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
