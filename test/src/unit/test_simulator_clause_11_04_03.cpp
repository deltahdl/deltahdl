// §11.4.3: Arithmetic operators


#include <cstring>

#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

// Shared fixture for expression evaluation tests.
static Expr* MakeInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr* MakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr* MakeBinary(Arena& arena, TokenKind op, Expr* lhs, Expr* rhs) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

static Variable* MakeVar4(SimFixture& f, std::string_view name,
                          uint32_t width, uint64_t aval, uint64_t bval) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}

static Variable* MakeRealVar(SimFixture& f, std::string_view name,
                             double val) {
  auto* var = f.ctx.CreateVariable(name, 64);
  uint64_t bits = 0;
  std::memcpy(&bits, &val, sizeof(double));
  var->value = MakeLogic4VecVal(f.arena, 64, bits);
  var->value.is_real = true;
  f.ctx.RegisterRealVariable(name);
  return var;
}

static double ToDouble(const Logic4Vec& v) {
  double d = 0.0;
  uint64_t bits = v.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

namespace {

// ==========================================================================
// Arithmetic X/Z propagation — §11.4.3
// ==========================================================================
TEST(EvalOpXZ, ArithAddX) {
  SimFixture f;
  // 4'b1x00 + 4'b0001 → all-X (any X/Z operand)
  MakeVar4(f, "ax", 4, 0b1000, 0b0100);  // 4'b1x00
  auto* b = f.ctx.CreateVariable("a1", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ax"),
                          MakeId(f.arena, "a1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, DivByZeroReturnsX) {
  SimFixture f;
  // 10 / 0 → all-X (not 0)
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeInt(f.arena, 10),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ModByZeroReturnsX) {
  SimFixture f;
  // 10 % 0 → all-X (not 0)
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeInt(f.arena, 10),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, RealArithResult) {
  SimFixture f;
  MakeRealVar(f, "ra", 2.5);
  MakeRealVar(f, "rb", 1.5);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ra"),
                          MakeId(f.arena, "rb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 4.0);
}

TEST(EvalOpXZ, MixedRealIntArith) {
  SimFixture f;
  // If either operand is real, both are converted to real.
  MakeRealVar(f, "re", 2.5);
  auto* vi = f.ctx.CreateVariable("ri", 32);
  vi->value = MakeLogic4VecVal(f.arena, 32, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "re"),
                          MakeId(f.arena, "ri"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 7.5);
}

// ==========================================================================
// Arithmetic X/Z — §11.4.3 (subtraction, multiply, power with X/Z)
// ==========================================================================
TEST(EvalOpXZ, ArithSubX) {
  SimFixture f;
  // 4'b1x00 - 1 → all-X (X/Z operand in subtraction)
  MakeVar4(f, "sx", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("s1", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "sx"),
                          MakeId(f.arena, "s1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ArithMulZ) {
  SimFixture f;
  // 4'b10z0 * 3 → all-X (Z operand in multiply)
  MakeVar4(f, "mz", 4, 0b1000, 0b0010);  // bit1=z (aval=0,bval=1)
  auto* b = f.ctx.CreateVariable("m3", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "mz"),
                          MakeId(f.arena, "m3"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ArithPowX) {
  SimFixture f;
  // 2 ** 4'b1x00 → all-X (X in exponent)
  MakeVar4(f, "px", 4, 0b1000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 2),
                          MakeId(f.arena, "px"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// § expression — binary addition
TEST(SimA83, BinaryAddition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd3 + 8'd7;\n"
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

// § expression — binary subtraction
TEST(SimA83, BinarySubtraction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10 - 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// § expression — binary multiplication
TEST(SimA83, BinaryMultiplication) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd5 * 8'd6;\n"
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

// § expression — unary bitwise NOT
TEST(SimA83, UnaryNegate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// =============================================================================
// A.8.6 Operators — unary_operator — Simulation
// =============================================================================
// § unary_operator — unary plus (identity)
TEST(SimA86, UnaryPlus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = +8'd42;\n"
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

// § unary_operator — unary minus (negate)
TEST(SimA86, UnaryMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -8'd1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// =============================================================================
// A.8.6 Operators — binary_operator (arithmetic) — Simulation
// =============================================================================
// § binary_operator — addition
TEST(SimA86, BinaryAdd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10 + 8'd20;\n"
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

// § binary_operator — subtraction
TEST(SimA86, BinarySub) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd30 - 8'd12;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 18u);
}

// § binary_operator — multiplication
TEST(SimA86, BinaryMul) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd7 * 8'd6;\n"
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

// § binary_operator — division
TEST(SimA86, BinaryDiv) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd100 / 8'd5;\n"
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

// § binary_operator — modulo
TEST(SimA86, BinaryMod) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd17 % 8'd5;\n"
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

// § binary_operator — power
TEST(SimA86, BinaryPower) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd2 ** 8'd5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 32u);
}

}  // namespace
