// §12.6: Pattern matching conditional statements — general concepts.

#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §12.6: Constant expression pattern — exact match returns 1.
TEST(Matches, ExactMatchTrue) {
  SimFixture f;
  auto* expr = ParseExprFrom("42 matches 42", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kBinary);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §12.6: Constant expression pattern — mismatch returns 0.
TEST(Matches, ExactMatchFalse) {
  SimFixture f;
  auto* expr = ParseExprFrom("42 matches 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §12.6: Variable value matched against constant pattern.
TEST(Matches, VariableMatch) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("sig", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  auto* expr = ParseExprFrom("sig matches 8'hAB", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §12.6: x/z bits in the pattern act as wildcards — matching is insensitive
// to those bit positions.
TEST(Matches, WildcardXInPattern) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("wv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = ParseExprFrom("wv matches 4'b1x1x", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // x bits in pattern are don't-cares, remaining bits match.
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §12.6: z/? bits in the pattern also act as wildcards.
TEST(Matches, WildcardZInPattern) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("zv", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = ParseExprFrom("zv matches 4'b1?0?", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §12.6: Pattern with wildcards but known bits mismatch → returns 0.
TEST(Matches, WildcardPatternMismatch) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("mm", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0b0010);
  // Known bit 3 in pattern is 1, but value has bit 3 = 0.
  auto* expr = ParseExprFrom("mm matches 4'b1x1x", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §12.6: Match result is always a determined 1-bit value (0 or 1), never x/z,
// even when the value contains x/z.
TEST(Matches, ResultAlwaysDetermined) {
  SimFixture f;
  MakeVar4(f, "xv", 4, 0b0000, 0b1111);  // All x
  auto* expr = ParseExprFrom("xv matches 4'b0000", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Result is 0 or 1, not x.
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.width, 1u);
}

// §12.6: case-matches with x/z wildcard in pattern — the case-matches path
// should use matches-style comparison, not exact 4-state comparison.
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
  // 4'b1010 matches 4'b1??? (? bits are wildcards) → second item.
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §12.6: case-matches with wildcard — value doesn't match any known bits.
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
  // 4'b1010 doesn't match 4'b0??0 (bit 3 differs) → default.
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

}  // namespace
