// Non-LRM tests

#include <gtest/gtest.h>
#include <cstring>
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


static Variable* MakeRealVar(EvalOpXZFixture& f, std::string_view name, double val) {
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

static std::string VecToStr(const Logic4Vec& vec) {
  std::string result;
  uint32_t nbytes = vec.width / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    result.push_back(ch);
  }
  return result;
}

static Variable* MakeStringVar(EvalOpXZFixture& f, std::string_view name,
                               std::string_view value) {
  uint32_t width = static_cast<uint32_t>(value.size()) * 8;
  if (width == 0) width = 8;
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  for (size_t i = 0; i < value.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(value.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    var->value.words[word].aval |=
        static_cast<uint64_t>(static_cast<unsigned char>(value[i])) << bit;
  }
  f.ctx.RegisterStringVariable(name);
  return var;
}
namespace {

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

TEST(EvalOpXZ, RelationalGtZ) {
  EvalOpXZFixture f;
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

TEST(EvalOpXZ, WildcardEqLeftX) {
  EvalOpXZFixture f;
  // §11.4.6: 4'bx001 ==? 4'b0001 → x (left X in non-wildcard position)
  MakeVar4(f, "wl", 4, 0b0001, 0b1000);  // bit3=x
  auto* b = f.ctx.CreateVariable("wr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b0001);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "wl"), MakeId(f.arena, "wr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
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

TEST(EvalOpXZ, ShiftLeftXOperand) {
  EvalOpXZFixture f;
  // 4'b1x00 << 1 → 4'bx000 (bval should shift with aval)
  MakeVar4(f, "so", 4, 0b1000, 0b0100);  // 4'b1x00
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "so"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // After << 1: aval=0b0000, bval=0b1000 (X shifted to bit3)
  EXPECT_EQ(result.words[0].aval & 0xFu, 0b0000u);
  EXPECT_EQ(result.words[0].bval & 0xFu, 0b1000u);
}

// ==========================================================================
// Ternary X/Z condition — §11.4.11
// ==========================================================================
TEST(EvalOpXZ, TernaryZCond) {
  EvalOpXZFixture f;
  // z ? 4'b1100 : 4'b1010 → same as x condition (bit-by-bit combine)
  MakeVar4(f, "tz", 1, 0, 1);  // 1'bz (aval=0, bval=1)
  auto* tv = f.ctx.CreateVariable("zt", 4);
  tv->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* fv = f.ctx.CreateVariable("zf", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "tz");
  ternary->true_expr = MakeId(f.arena, "zt");
  ternary->false_expr = MakeId(f.arena, "zf");
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  // Same as TernaryXCondDiff: aval=0b1000, bval=0b0110
  EXPECT_EQ(result.words[0].aval, 0b1000u);
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

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

// Signed comparison, signed arithmetic, expression type rules
// moved to test_eval_advanced.cpp
// ==========================================================================
// Logical implication (->) and equivalence (<->) — §11.4.7
// ==========================================================================
TEST(EvalOpXZ, ImplTT) {
  EvalOpXZFixture f;
  // 1 -> 1 = 1
  MakeVar4(f, "it1", 1, 1, 0);
  MakeVar4(f, "it2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, ImplTF) {
  EvalOpXZFixture f;
  // 1 -> 0 = 0
  MakeVar4(f, "it1", 1, 1, 0);
  MakeVar4(f, "it2", 1, 0, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, ImplFT) {
  EvalOpXZFixture f;
  // 0 -> 1 = 1 (vacuous truth)
  MakeVar4(f, "it1", 1, 0, 0);
  MakeVar4(f, "it2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, ImplFF) {
  EvalOpXZFixture f;
  // 0 -> 0 = 1 (vacuous truth)
  MakeVar4(f, "it1", 1, 0, 0);
  MakeVar4(f, "it2", 1, 0, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, ImplXT) {
  EvalOpXZFixture f;
  // x -> 1 = 1 (since !x || 1 = 1 regardless of x)
  MakeVar4(f, "ix1", 1, 0, 1);  // 1'bx
  MakeVar4(f, "ix2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ix1"),
                          MakeId(f.arena, "ix2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ImplXF) {
  EvalOpXZFixture f;
  // x -> 0 = x (since !x || 0 = !x, and !x is x when x is unknown)
  MakeVar4(f, "ix1", 1, 0, 1);  // 1'bx
  MakeVar4(f, "ix2", 1, 0, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ix1"),
                          MakeId(f.arena, "ix2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is x
}

TEST(EvalOpXZ, EquivSame) {
  EvalOpXZFixture f;
  // 1 <-> 1 = 1
  MakeVar4(f, "eq1", 1, 1, 0);
  MakeVar4(f, "eq2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "eq1"),
                          MakeId(f.arena, "eq2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, EquivDiff) {
  EvalOpXZFixture f;
  // 1 <-> 0 = 0
  MakeVar4(f, "eq1", 1, 1, 0);
  MakeVar4(f, "eq2", 1, 0, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "eq1"),
                          MakeId(f.arena, "eq2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, EquivX) {
  EvalOpXZFixture f;
  // x <-> 1 = x
  MakeVar4(f, "ex1", 1, 0, 1);  // 1'bx
  MakeVar4(f, "ex2", 1, 1, 0);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "ex1"),
                          MakeId(f.arena, "ex2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is x
}

// ==========================================================================
// MinTypMax evaluation — §11.11
// ==========================================================================
TEST(EvalOpXZ, MinTypMaxDefaultTyp) {
  EvalOpXZFixture f;
  // Default delay mode is typ — should return middle expression.
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);        // min
  mtm->condition = MakeInt(f.arena, 20);  // typ
  mtm->rhs = MakeInt(f.arena, 30);        // max
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

TEST(EvalOpXZ, MinTypMaxMin) {
  EvalOpXZFixture f;
  f.ctx.SetDelayMode(DelayMode::kMin);
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);
  mtm->condition = MakeInt(f.arena, 20);
  mtm->rhs = MakeInt(f.arena, 30);
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
}

TEST(EvalOpXZ, MinTypMaxMax) {
  EvalOpXZFixture f;
  f.ctx.SetDelayMode(DelayMode::kMax);
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);
  mtm->condition = MakeInt(f.arena, 20);
  mtm->rhs = MakeInt(f.arena, 30);
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 30u);
}

// ==========================================================================
// Bit-select/part-select X/Z address — §11.5.1
// ==========================================================================
TEST(EvalOpXZ, BitSelectXAddr) {
  EvalOpXZFixture f;
  // v[x] should return 1'bx when index is unknown.
  auto* v = f.ctx.CreateVariable("bsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  MakeVar4(f, "bsi", 4, 0, 1);  // 4'bx (unknown index)
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bsv");
  sel->index = MakeId(f.arena, "bsi");
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_NE(result.words[0].bval, 0u);  // result is x
}

TEST(EvalOpXZ, PartSelectXAddr) {
  EvalOpXZFixture f;
  // v[x +: 4] should return all-x when base index is unknown.
  auto* v = f.ctx.CreateVariable("psv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  MakeVar4(f, "psi", 4, 0, 1);  // unknown index
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "psv");
  sel->index = MakeId(f.arena, "psi");
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_NE(result.words[0].bval, 0u);  // result has x bits
}

// ==========================================================================
// Context-determined bit widths — §11.6.1
// ==========================================================================
TEST(EvalOpXZ, WidthPropFromContext) {
  EvalOpXZFixture f;
  // 4-bit a + 4-bit b with 8-bit context → 8-bit result (no overflow).
  auto* va = f.ctx.CreateVariable("wa", 4);
  va->value = MakeLogic4VecVal(f.arena, 4, 0xF);
  auto* vb = f.ctx.CreateVariable("wb", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "wa"),
                          MakeId(f.arena, "wb"));
  // Without context width: 4-bit result overflows to 0.
  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0u);
  // With context width 8: 8-bit result = 0x10.
  auto r2 = EvalExpr(expr, f.ctx, f.arena, 8);
  EXPECT_EQ(r2.ToUint64(), 0x10u);
  EXPECT_EQ(r2.width, 8u);
}

TEST(EvalOpXZ, TernaryWidthFromBranches) {
  EvalOpXZFixture f;
  // ?: width = max(true_width, false_width)
  auto* cond = f.ctx.CreateVariable("tc", 1);
  cond->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* tv = f.ctx.CreateVariable("tv", 8);
  tv->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  auto* fv = f.ctx.CreateVariable("fv", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0xA);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "tc");
  tern->true_expr = MakeId(f.arena, "tv");
  tern->false_expr = MakeId(f.arena, "fv");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  // Width should be max(8,4) = 8, value 0xFF.
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(EvalOpXZ, RealArithResult) {
  EvalOpXZFixture f;
  MakeRealVar(f, "ra", 2.5);
  MakeRealVar(f, "rb", 1.5);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ra"),
                          MakeId(f.arena, "rb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_TRUE(result.is_real);
  EXPECT_DOUBLE_EQ(ToDouble(result), 4.0);
}

TEST(EvalOpXZ, RealComparisonSingleBit) {
  EvalOpXZFixture f;
  MakeRealVar(f, "rc", 3.14);
  MakeRealVar(f, "rd", 2.71);
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "rc"),
                          MakeId(f.arena, "rd"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, MixedRealIntArith) {
  EvalOpXZFixture f;
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

TEST(EvalOpXZ, StringConcatDataType) {
  EvalOpXZFixture f;
  MakeStringVar(f, "s1", "hello");
  MakeStringVar(f, "s2", " world");
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "s1"));
  concat->elements.push_back(MakeId(f.arena, "s2"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(VecToStr(result), "hello world");
}

TEST(EvalOpXZ, StringReplicateRuntime) {
  EvalOpXZFixture f;
  MakeStringVar(f, "sr", "ab");
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 3);
  repl->elements.push_back(MakeId(f.arena, "sr"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_EQ(VecToStr(result), "ababab");
}

// ==========================================================================
// Arithmetic X/Z — §11.4.3 (subtraction, multiply, power with X/Z)
// ==========================================================================
TEST(EvalOpXZ, ArithSubX) {
  EvalOpXZFixture f;
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
  EvalOpXZFixture f;
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
  EvalOpXZFixture f;
  // 2 ** 4'b1x00 → all-X (X in exponent)
  MakeVar4(f, "px", 4, 0b1000, 0b0100);
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 2),
                          MakeId(f.arena, "px"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// ==========================================================================
// §6.16: String data type detection in concatenation/replication
// ==========================================================================
TEST(EvalOpXZ, StringConcatSetsIsString) {
  EvalOpXZFixture f;
  MakeStringVar(f, "sa", "hi");
  MakeStringVar(f, "sb", "lo");
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "sa"));
  concat->elements.push_back(MakeId(f.arena, "sb"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
}

TEST(EvalOpXZ, NonStringConcatNotIsString) {
  EvalOpXZFixture f;
  auto* a = f.ctx.CreateVariable("ia", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 0x41);
  auto* b = f.ctx.CreateVariable("ib", 8);
  b->value = MakeLogic4VecVal(f.arena, 8, 0x42);
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "ia"));
  concat->elements.push_back(MakeId(f.arena, "ib"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_FALSE(result.is_string);
}

TEST(EvalOpXZ, StringReplicateSetsIsString) {
  EvalOpXZFixture f;
  MakeStringVar(f, "sr2", "ab");
  auto* repl = f.arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = MakeInt(f.arena, 2);
  repl->elements.push_back(MakeId(f.arena, "sr2"));
  auto result = EvalExpr(repl, f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
}

TEST(EvalOpXZ, IdentifierStringPropagation) {
  EvalOpXZFixture f;
  MakeStringVar(f, "sv2", "test");
  auto result = EvalExpr(MakeId(f.arena, "sv2"), f.ctx, f.arena);
  EXPECT_TRUE(result.is_string);
}

}  // namespace
