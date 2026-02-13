#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// Shared fixture for expression evaluation tests.
struct EvalOpXZFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

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

static Expr* MakeUnary(Arena& arena, TokenKind op, Expr* operand) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kUnary;
  e->op = op;
  e->lhs = operand;
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

static Variable* MakeVar4(EvalOpXZFixture& f, std::string_view name,
                          uint32_t width, uint64_t aval, uint64_t bval) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}

// ==========================================================================
// Inside operator X/Z — §11.4.13
// ==========================================================================

TEST(EvalOpXZ, InsideXOperand) {
  EvalOpXZFixture f;
  // x inside {3, 5, 7} → x (unknown operand, no definite match)
  MakeVar4(f, "ix", 4, 0b0000, 0b0100);  // 4'b0x00

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "ix");
  inside->elements.push_back(MakeInt(f.arena, 3));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 7));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// ==========================================================================
// Relational X/Z propagation — §11.4.4
// ==========================================================================

TEST(EvalOpXZ, RelationalLtX) {
  EvalOpXZFixture f;
  // 4'b1x00 < 4'b1010 → x
  MakeVar4(f, "rl", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("rr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "rl"),
                          MakeId(f.arena, "rr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, RelationalKnownStillWorks) {
  EvalOpXZFixture f;
  // 3 < 5 → 1 (known values still work)
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeInt(f.arena, 3),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

// ==========================================================================
// Equality X/Z propagation — §11.4.5, §11.4.6
// ==========================================================================

TEST(EvalOpXZ, LogicalEqX) {
  EvalOpXZFixture f;
  // 4'b1x00 == 4'b1100 → x
  MakeVar4(f, "el", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("er", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "el"),
                          MakeId(f.arena, "er"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalNeqX) {
  EvalOpXZFixture f;
  // 4'b1x00 != 4'b1100 → x
  MakeVar4(f, "nl", 4, 0b1000, 0b0100);
  auto* b = f.ctx.CreateVariable("nr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "nl"),
                          MakeId(f.arena, "nr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, CaseEqStillExact) {
  EvalOpXZFixture f;
  // === still compares aval+bval exactly, no X propagation
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqEq, MakeInt(f.arena, 5),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

// ==========================================================================
// Logical operator X/Z — §11.4.7
// ==========================================================================

TEST(EvalOpXZ, LogicalNotX) {
  EvalOpXZFixture f;
  // !4'b1x00 → x
  MakeVar4(f, "ln", 4, 0b1000, 0b0100);
  auto* expr = MakeUnary(f.arena, TokenKind::kBang, MakeId(f.arena, "ln"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndZeroX) {
  EvalOpXZFixture f;
  // 0 && x → 0 (short-circuit: lhs known-0 → result 0)
  MakeVar4(f, "lx", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeInt(f.arena, 0),
                          MakeId(f.arena, "lx"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndXZero) {
  EvalOpXZFixture f;
  // x && 0 → 0 (rhs known-0 → result 0 despite lhs unknown)
  MakeVar4(f, "ax", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeId(f.arena, "ax"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndXX) {
  EvalOpXZFixture f;
  // x && 1 → x
  MakeVar4(f, "bx", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeId(f.arena, "bx"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalOrOneX) {
  EvalOpXZFixture f;
  // 1 || x → 1 (short-circuit: lhs known-1 → result 1)
  MakeVar4(f, "ox", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeInt(f.arena, 1),
                          MakeId(f.arena, "ox"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalOrXOne) {
  EvalOpXZFixture f;
  // x || 1 → 1
  MakeVar4(f, "px", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeId(f.arena, "px"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalOrXX) {
  EvalOpXZFixture f;
  // x || 0 → x
  MakeVar4(f, "qx", 4, 0b0000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeId(f.arena, "qx"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// ==========================================================================
// Shift X/Z propagation — §11.4.10
// ==========================================================================

TEST(EvalOpXZ, ShiftXAmount) {
  EvalOpXZFixture f;
  // 4'b1100 << x → all-X
  MakeVar4(f, "sa", 4, 0b0000, 0b0100);  // x shift amount
  auto* a = f.ctx.CreateVariable("sv", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "sv"),
                          MakeId(f.arena, "sa"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// ==========================================================================
// Ternary X/Z condition — §11.4.11
// ==========================================================================

TEST(EvalOpXZ, TernaryXCondSame) {
  EvalOpXZFixture f;
  // x ? 5 : 5 → 5 (both branches same → known result)
  MakeVar4(f, "tc", 1, 0, 1);  // 1'bx
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "tc");
  ternary->true_expr = MakeInt(f.arena, 5);
  ternary->false_expr = MakeInt(f.arena, 5);
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, TernaryXCondDiff) {
  EvalOpXZFixture f;
  // x ? 4'b1100 : 4'b1010 → 4'b1x0x (matching bits kept, differing → X)
  MakeVar4(f, "td", 1, 0, 1);  // 1'bx
  auto* tv = f.ctx.CreateVariable("tt", 4);
  tv->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* fv = f.ctx.CreateVariable("tf", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "td");
  ternary->true_expr = MakeId(f.arena, "tt");
  ternary->false_expr = MakeId(f.arena, "tf");
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  // 4'b1x0x: bits that match keep value, bits that differ → X
  //   bit3: 1==1 → 1 (aval=1, bval=0)
  //   bit2: 1!=0 → x (aval=0, bval=1)
  //   bit1: 0!=1 → x (aval=0, bval=1)
  //   bit0: 0==0 → 0 (aval=0, bval=0)
  // aval=0b1000, bval=0b0110
  EXPECT_EQ(result.words[0].aval, 0b1000u);
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

// ==========================================================================
// Reduction X/Z propagation — §11.4.9
// ==========================================================================

TEST(EvalOpXZ, ReductionAndWithX) {
  EvalOpXZFixture f;
  // &4'b1x11 → x (not all bits known-1)
  MakeVar4(f, "ra", 4, 0b1011, 0b0100);  // bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "ra"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

TEST(EvalOpXZ, ReductionAndWithKnown0) {
  EvalOpXZFixture f;
  // &4'b0x11 → 0 (known-0 bit forces result to 0)
  MakeVar4(f, "rb", 4, 0b0011, 0b0100);  // bit3=0, bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "rb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 0u);
  EXPECT_EQ(result.words[0].bval, 0u);  // known-0
}

TEST(EvalOpXZ, ReductionOrWithKnown1) {
  EvalOpXZFixture f;
  // |4'b1x00 → 1 (known-1 bit forces result to 1)
  MakeVar4(f, "rc", 4, 0b1000, 0b0100);  // bit3=1, bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rc"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.words[0].aval, 1u);
  EXPECT_EQ(result.words[0].bval, 0u);  // known-1
}

TEST(EvalOpXZ, ReductionOrWithX) {
  EvalOpXZFixture f;
  // |4'b0x00 → x (no known-1, but X could be 1)
  MakeVar4(f, "rd", 4, 0b0000, 0b0100);  // all 0 except bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeId(f.arena, "rd"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

TEST(EvalOpXZ, ReductionXorWithX) {
  EvalOpXZFixture f;
  // ^4'b1x10 → x (any X/Z in XOR → X)
  MakeVar4(f, "re", 4, 0b1010, 0b0100);  // bit2=x
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeId(f.arena, "re"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

// ==========================================================================
// Arithmetic X/Z propagation — §11.4.3
// ==========================================================================

TEST(EvalOpXZ, ArithAddX) {
  EvalOpXZFixture f;
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
  EvalOpXZFixture f;
  // 10 / 0 → all-X (not 0)
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeInt(f.arena, 10),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ModByZeroReturnsX) {
  EvalOpXZFixture f;
  // 10 % 0 → all-X (not 0)
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeInt(f.arena, 10),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// ==========================================================================
// Binary XNOR (^~, ~^) — §11.4.8
// ==========================================================================

TEST(EvalOpXZ, BinaryXnorBasic) {
  EvalOpXZFixture f;
  // 4'b1100 ^~ 4'b1010 = 4'b1001 = 9
  auto* a = f.ctx.CreateVariable("xa", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* b = f.ctx.CreateVariable("xb", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);

  auto* expr = MakeBinary(f.arena, TokenKind::kTildeCaret,
                          MakeId(f.arena, "xa"), MakeId(f.arena, "xb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 0b1001u);
}

TEST(EvalOpXZ, BinaryXnorCaretTilde) {
  EvalOpXZFixture f;
  // 4'b1100 ~^ 4'b1010 = 4'b1001 = 9 (same as ^~)
  auto* a = f.ctx.CreateVariable("ya", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* b = f.ctx.CreateVariable("yb", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);

  auto* expr = MakeBinary(f.arena, TokenKind::kCaretTilde,
                          MakeId(f.arena, "ya"), MakeId(f.arena, "yb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 0b1001u);
}

TEST(EvalOpXZ, BinaryXnorWithX) {
  EvalOpXZFixture f;
  // 4'b1x00 ^~ 4'b1010: result 4'b1x01
  auto* a = f.ctx.CreateVariable("za", 4);
  a->value = MakeLogic4Vec(f.arena, 4);
  a->value.words[0].aval = 0b1000;
  a->value.words[0].bval = 0b0100;

  auto* b = f.ctx.CreateVariable("zb", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b1010);

  auto* expr = MakeBinary(f.arena, TokenKind::kTildeCaret,
                          MakeId(f.arena, "za"), MakeId(f.arena, "zb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.words[0].aval, 0b1001u);
  EXPECT_EQ(result.words[0].bval, 0b0100u);
}

// ==========================================================================
// Signed comparison — §11.4.4, §11.4.5, §11.8.1
// ==========================================================================

// Helper: create a signed variable.
static Variable* MakeSignedVar(EvalOpXZFixture& f, std::string_view name,
                               uint32_t width, uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  var->is_signed = true;
  return var;
}

TEST(EvalOpXZ, SignedLtNeg) {
  EvalOpXZFixture f;
  // -1 (8'hFF signed) < 1 (8'h01 signed) → 1 (true)
  // As unsigned: 255 < 1 → 0 (false)
  MakeSignedVar(f, "sa", 8, 0xFF);
  MakeSignedVar(f, "sb", 8, 0x01);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);  // -1 < 1 → true
}

TEST(EvalOpXZ, SignedGtNeg) {
  EvalOpXZFixture f;
  // 1 (8'h01 signed) > -1 (8'hFF signed) → 1 (true)
  MakeSignedVar(f, "sa", 8, 0x01);
  MakeSignedVar(f, "sb", 8, 0xFF);
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);  // 1 > -1 → true
}

TEST(EvalOpXZ, SignedEqNeg) {
  EvalOpXZFixture f;
  // -1 (8'hFF signed) == -1 (8'hFF signed) → 1
  MakeSignedVar(f, "sa", 8, 0xFF);
  MakeSignedVar(f, "sb", 8, 0xFF);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, UnsignedLtUnchanged) {
  EvalOpXZFixture f;
  // 0xFF (unsigned) < 0x01 (unsigned) → 0 (false, 255 > 1)
  auto* a = f.ctx.CreateVariable("ua", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  auto* b = f.ctx.CreateVariable("ub", 8);
  b->value = MakeLogic4VecVal(f.arena, 8, 0x01);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "ua"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);  // 255 < 1 → false
}

// ==========================================================================
// Signed arithmetic — §11.4.3, §11.4.3.1
// ==========================================================================

TEST(EvalOpXZ, SignedDivTruncToZero) {
  EvalOpXZFixture f;
  // -7 / 2 = -3 (truncation toward zero, not -4)
  // -7 as 8-bit signed = 0xF9
  MakeSignedVar(f, "sd", 8, 0xF9);
  MakeSignedVar(f, "se", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "sd"),
                          MakeId(f.arena, "se"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // -3 as 8-bit = 0xFD
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFDu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalOpXZ, SignedModSignOfFirst) {
  EvalOpXZFixture f;
  // -7 % 2 = -1 (sign of dividend per IEEE)
  MakeSignedVar(f, "sm", 8, 0xF9);
  MakeSignedVar(f, "sn", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "sm"),
                          MakeId(f.arena, "sn"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // -1 as 8-bit = 0xFF
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalOpXZ, SignedMulNeg) {
  EvalOpXZFixture f;
  // -3 * 4 = -12. -3 as 8-bit = 0xFD, -12 as 8-bit = 0xF4
  MakeSignedVar(f, "ma", 8, 0xFD);
  MakeSignedVar(f, "mb", 8, 4);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "ma"),
                          MakeId(f.arena, "mb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xF4u);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalOpXZ, UnsignedDivUnchanged) {
  EvalOpXZFixture f;
  // 0xF9 / 2 = 124 (unsigned: 249 / 2 = 124)
  auto* a = f.ctx.CreateVariable("ud", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 0xF9);
  auto* b = f.ctx.CreateVariable("ue", 8);
  b->value = MakeLogic4VecVal(f.arena, 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "ud"),
                          MakeId(f.arena, "ue"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 124u);  // 249 / 2 = 124
}
