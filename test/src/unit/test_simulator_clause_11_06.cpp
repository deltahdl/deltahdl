#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

// §11.6: LHS width determines context for RHS expression evaluation.
// When LHS is wider than self-determined RHS width, carry is preserved.
TEST(SimA116, AssignmentContextWidthPreservesCarry) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] sumB;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumB = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumB");
  ASSERT_NE(var, nullptr);
  // §11.6: sumB is 17 bits, so a+b evaluates using 17 bits, preserving carry.
  EXPECT_EQ(var->value.ToUint64(), 0x10000u);
}

// §11.6: When LHS width equals operand width, no extra bits.
TEST(SimA116, AssignmentContextWidthSameSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] sumA;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    sumA = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sumA");
  ASSERT_NE(var, nullptr);
  // §11.6: sumA is 16 bits, so a+b evaluates using 16 bits, carry truncated.
  EXPECT_EQ(var->value.ToUint64(), 0x0000u);
}

// §11.6: Context width propagates through binary arithmetic.
TEST(SimA116, ContextWidthPropagatesForMultiplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    result = a * a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // §11.6: result is 8 bits, a*a self-determined is 4 bits.
  // With 8-bit context: 15 * 15 = 225 = 0xE1.
  EXPECT_EQ(var->value.ToUint64(), 0xE1u);
}

// §11.6: Context width from unit-level EvalExpr parameter.
TEST(SimA116, ContextWidthParamInEvalExpr) {
  SimFixture f;

  MakeVar(f, "ca", 4, 0xF);
  MakeVar(f, "cb", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ca"),
                          MakeId(f.arena, "cb"));

  // Self-determined: 4 bits, overflow → 0.
  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0u);

  // Context-determined: 5 bits, carry preserved → 0x10.
  auto r2 = EvalExpr(expr, f.ctx, f.arena, 5);
  EXPECT_EQ(r2.ToUint64(), 0x10u);
  EXPECT_EQ(r2.width, 5u);
}

// §11.6: Casting sets the size context of an intermediate value.
TEST(SimA116, CastingSetsContextWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic [15:0] answer;\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    answer = (a + b + 0) >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("answer");
  ASSERT_NE(var, nullptr);
  // §11.6.2: Adding 0 (unsized integer, ≥32 bits) forces evaluation at 32 bits.
  // (0xFFFF + 1 + 0) = 0x10000, >> 1 = 0x8000.
  EXPECT_EQ(var->value.ToUint64(), 0x8000u);
}

// §11.6: Subtraction with wider LHS preserves borrow.
TEST(SimA116, SubtractionContextWidthPreservesBorrow) {
  SimFixture f;

  MakeVar(f, "sa", 8, 0);
  MakeVar(f, "sb", 8, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));

  // Self-determined 8-bit: 0 - 1 = 0xFF (unsigned underflow).
  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0xFFu);
  EXPECT_EQ(r1.width, 8u);

  // With 16-bit context: 0 - 1 = 0xFFFF (16-bit unsigned wrap).
  auto r2 = EvalExpr(expr, f.ctx, f.arena, 16);
  EXPECT_EQ(r2.ToUint64(), 0xFFFFu);
  EXPECT_EQ(r2.width, 16u);
}

}  // namespace
