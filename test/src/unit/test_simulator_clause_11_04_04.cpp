// §11.4.4: Relational operators

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// ==========================================================================
// Relational X/Z propagation — §11.4.4
// ==========================================================================
TEST(EvalOpXZ, RelationalLtX) {
  SimFixture f;
  // 4'b1x00 < 4'b1010 → x
  MakeVar4(f, "rl", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("rr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "rl"),
                          MakeId(f.arena, "rr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, RelationalGtZ) {
  SimFixture f;
  // 4'b10z0 > 4'b1000 → x (Z operand)
  MakeVar4(f, "gz", 4, 0b1000, 0b0010);  // bit1=z
  auto* b = f.ctx.CreateVariable("g8", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1000);
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "gz"),
                          MakeId(f.arena, "g8"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

TEST(EvalOpXZ, RelationalKnownStillWorks) {
  SimFixture f;
  // 3 < 5 → 1 (known values still work)
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeInt(f.arena, 3),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, RealComparisonSingleBit) {
  SimFixture f;
  MakeRealVar(f, "rc", 3.14);
  MakeRealVar(f, "rd", 2.71);
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "rc"),
                          MakeId(f.arena, "rd"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// =============================================================================
// A.8.6 Operators — binary_operator (relational) — Simulation
// =============================================================================
// § binary_operator — < (less than)
TEST(SimA86, BinaryLessThan) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd3 < 8'd5);\n"
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

// § binary_operator — > (greater than)
TEST(SimA86, BinaryGreaterThan) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd10 > 8'd3);\n"
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

// § binary_operator — >= (greater or equal)
TEST(SimA86, BinaryGreaterOrEqual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 >= 8'd5);\n"
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

}  // namespace
