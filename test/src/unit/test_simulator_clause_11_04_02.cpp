// §11.4.2: Increment and decrement operators

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/eval.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.3 Expressions — Simulation
// =============================================================================
// § inc_or_dec_expression — prefix increment
TEST(SimA83, PrefixIncrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; ++x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

// § inc_or_dec_expression — prefix decrement
TEST(SimA83, PrefixDecrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; --x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

// § inc_or_dec_expression — postfix increment
TEST(SimA83, PostfixIncrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; x++; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

// § inc_or_dec_expression — postfix decrement
TEST(SimA83, PostfixDecrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd10; x--; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

// § variable_lvalue — pre-increment
TEST(SimA85, VarLvaluePreIncrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin x = 10; ++x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

// § variable_lvalue — post-decrement
TEST(SimA85, VarLvaluePostDecrement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin x = 10; x--; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 9u);
}

static double AdvToDouble(const Logic4Vec& v) {
  double d = 0.0;
  uint64_t bits = v.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

static Variable* MakeRealVarAdv(SimFixture& f, std::string_view name,
                                double val) {
  auto* var = f.ctx.CreateVariable(name, 64);
  uint64_t bits = 0;
  std::memcpy(&bits, &val, sizeof(double));
  var->value = MakeLogic4VecVal(f.arena, 64, bits);
  var->value.is_real = true;
  f.ctx.RegisterRealVariable(name);
  return var;
}

TEST(EvalAdv, RealIncrementBy1Point0) {
  SimFixture f;
  // §11.4.2: ++real_var should increment by 1.0, not by integer 1.
  MakeRealVarAdv(f, "rv", 2.5);
  auto* inc = f.arena.Create<Expr>();
  inc->kind = ExprKind::kUnary;
  inc->op = TokenKind::kPlusPlus;
  inc->lhs = MakeId(f.arena, "rv");
  auto result = EvalExpr(inc, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(AdvToDouble(result), 3.5);
}

}  // namespace
