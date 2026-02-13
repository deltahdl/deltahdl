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
struct EvalOpFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// Helper: build a simple integer literal Expr node.
static Expr* MakeInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper: build an identifier Expr node.
static Expr* MakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper: build a unary Expr.
static Expr* MakeUnary(Arena& arena, TokenKind op, Expr* operand) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kUnary;
  e->op = op;
  e->lhs = operand;
  return e;
}

// Helper: build a binary Expr.
static Expr* MakeBinary(Arena& arena, TokenKind op, Expr* lhs, Expr* rhs) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

// ==========================================================================
// Reduction operators (unary &, |, ^, ~&, ~|, ~^, ^~)
// ==========================================================================

TEST(EvalOp, ReductionAndAllOnes) {
  EvalOpFixture f;
  // &32'hFFFFFFFF = 1 (all 32 bits are 1)
  auto* expr =
      MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0xFFFFFFFF));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionAndNotAllOnes) {
  EvalOpFixture f;
  // &32'd5 = 0 (not all bits 1)
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionOrNonZero) {
  EvalOpFixture f;
  // |32'd4 = 1
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionOrZero) {
  EvalOpFixture f;
  // |32'd0 = 0
  auto* expr = MakeUnary(f.arena, TokenKind::kPipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionXorEvenOnes) {
  EvalOpFixture f;
  // ^32'd3 = 0 (two 1-bits => even parity)
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, ReductionXorOddOnes) {
  EvalOpFixture f;
  // ^32'd7 = 1 (three 1-bits => odd parity)
  auto* expr = MakeUnary(f.arena, TokenKind::kCaret, MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionNand) {
  EvalOpFixture f;
  // ~&32'd5 = 1 (not all bits 1)
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeAmp, MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionNor) {
  EvalOpFixture f;
  // ~|32'd0 = 1
  auto* expr = MakeUnary(f.arena, TokenKind::kTildePipe, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionXnorTildeCaret) {
  EvalOpFixture f;
  // ~^32'd3 = 1 (even parity -> XNOR=1)
  auto* expr = MakeUnary(f.arena, TokenKind::kTildeCaret, MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, ReductionXnorCaretTilde) {
  EvalOpFixture f;
  // ^~32'd7 = 0 (odd parity -> XNOR=0)
  auto* expr = MakeUnary(f.arena, TokenKind::kCaretTilde, MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ==========================================================================
// Replication ({n{expr}})
// ==========================================================================

TEST(EvalOp, Replicate3Times) {
  EvalOpFixture f;
  // {3{4'b1010}} = 12'b1010_1010_1010 = 0xAAA
  auto* var = f.ctx.CreateVariable("v", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0xA);

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 3);
  rep->elements.push_back(MakeId(f.arena, "v"));
  auto result = EvalExpr(rep, f.ctx, f.arena);
  // 3 * 4 = 12 bits, value = 0xAAA
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0xAAAu);
}

TEST(EvalOp, ReplicateOnce) {
  EvalOpFixture f;
  // {1{8'd42}} = 42
  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 1);
  rep->elements.push_back(MakeInt(f.arena, 42));
  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

// ==========================================================================
// Power operator (**)
// ==========================================================================

TEST(EvalOp, PowerBasic) {
  EvalOpFixture f;
  // 2 ** 10 = 1024
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 2),
                          MakeInt(f.arena, 10));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1024u);
}

TEST(EvalOp, PowerZeroExponent) {
  EvalOpFixture f;
  // 5 ** 0 = 1
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 5),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, PowerOneExponent) {
  EvalOpFixture f;
  // 7 ** 1 = 7
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 7),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

// ==========================================================================
// Wildcard equality (==?, !=?)
// ==========================================================================

TEST(EvalOp, WildcardEqMatch) {
  EvalOpFixture f;
  // 5 ==? 5 = 1 (no X/Z bits, exact match)
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, WildcardEqMismatch) {
  EvalOpFixture f;
  // 5 ==? 3 = 0
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, WildcardNeqMatch) {
  EvalOpFixture f;
  // 5 !=? 3 = 1
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, WildcardNeqSame) {
  EvalOpFixture f;
  // 5 !=? 5 = 0
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ==========================================================================
// Postfix increment/decrement (i++, i--)
// ==========================================================================

// ==========================================================================
// Prefix increment/decrement (++i, --i)
// ==========================================================================

TEST(EvalOp, PrefixIncrement) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("i", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* pre = MakeUnary(f.arena, TokenKind::kPlusPlus, MakeId(f.arena, "i"));

  auto result = EvalExpr(pre, f.ctx, f.arena);
  // Returns NEW value (prefix semantics).
  EXPECT_EQ(result.ToUint64(), 11u);
  // Variable is now 11.
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(EvalOp, PrefixDecrement) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("j", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 5);

  auto* pre = MakeUnary(f.arena, TokenKind::kMinusMinus, MakeId(f.arena, "j"));

  auto result = EvalExpr(pre, f.ctx, f.arena);
  // Returns NEW value.
  EXPECT_EQ(result.ToUint64(), 4u);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(EvalOp, PostfixIncrement) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("i", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* post = f.arena.Create<Expr>();
  post->kind = ExprKind::kPostfixUnary;
  post->op = TokenKind::kPlusPlus;
  post->lhs = MakeId(f.arena, "i");

  auto result = EvalExpr(post, f.ctx, f.arena);
  // Returns original value.
  EXPECT_EQ(result.ToUint64(), 10u);
  // Variable is now 11.
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(EvalOp, PostfixDecrement) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("j", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 5);

  auto* post = f.arena.Create<Expr>();
  post->kind = ExprKind::kPostfixUnary;
  post->op = TokenKind::kMinusMinus;
  post->lhs = MakeId(f.arena, "j");

  auto result = EvalExpr(post, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// ==========================================================================
// Compound assignment operators (+=, -=, *=, /=, %=, &=, |=, ^=, <<=, >>=)
// ==========================================================================

TEST(EvalOp, PlusEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* expr = MakeBinary(f.arena, TokenKind::kPlusEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 15u);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(EvalOp, MinusEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 20);

  auto* expr = MakeBinary(f.arena, TokenKind::kMinusEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 13u);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(EvalOp, StarEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 6);

  auto* expr = MakeBinary(f.arena, TokenKind::kStarEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(EvalOp, SlashEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 100);

  auto* expr = MakeBinary(f.arena, TokenKind::kSlashEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(EvalOp, AmpEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto* expr = MakeBinary(f.arena, TokenKind::kAmpEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 0x0F));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0Fu);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(EvalOp, PipeEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xF0);

  auto* expr = MakeBinary(f.arena, TokenKind::kPipeEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 0x0F));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(EvalOp, CaretEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto* expr = MakeBinary(f.arena, TokenKind::kCaretEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 0x0F));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xF0u);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

TEST(EvalOp, LtLtEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(EvalOp, GtGtEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 256);

  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

// ==========================================================================
// Member access (struct_var.field)
// ==========================================================================

TEST(EvalOp, MemberAccessBasic) {
  EvalOpFixture f;
  // Simulate a struct with a 32-bit field stored as a variable "s.x".
  auto* var = f.ctx.CreateVariable("s.x", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 99);

  auto* acc = f.arena.Create<Expr>();
  acc->kind = ExprKind::kMemberAccess;
  acc->lhs = MakeId(f.arena, "s");
  acc->rhs = MakeId(f.arena, "x");

  auto result = EvalExpr(acc, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

// ==========================================================================
// Cast (type'(expr))
// ==========================================================================

TEST(EvalOp, CastTruncate) {
  EvalOpFixture f;
  // Cast a 32-bit value to a narrower type (truncate).
  // We test by evaluating the inner expression and checking the result.
  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "byte";                  // 8-bit type
  cast->lhs = MakeInt(f.arena, 0x1FF);  // 511

  auto result = EvalExpr(cast, f.ctx, f.arena);
  // byte is 8-bit: 0x1FF & 0xFF = 0xFF = 255
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(result.width, 8u);
}

TEST(EvalOp, CastWiden) {
  EvalOpFixture f;
  // Cast to int (32-bit) — value should be preserved.
  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "int";
  cast->lhs = MakeInt(f.arena, 42);

  auto result = EvalExpr(cast, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(result.width, 32u);
}

// ==========================================================================
// Inside operator (expr inside {val1, val2, [lo:hi]})
// ==========================================================================

TEST(EvalOp, InsideMatch) {
  EvalOpFixture f;
  // 5 inside {3, 5, 7} = 1
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 5);
  inside->elements.push_back(MakeInt(f.arena, 3));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 7));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideNoMatch) {
  EvalOpFixture f;
  // 4 inside {3, 5, 7} = 0
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 4);
  inside->elements.push_back(MakeInt(f.arena, 3));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 7));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, InsideRange) {
  EvalOpFixture f;
  // 5 inside {[3:7]} = 1 (range element)
  auto* range = f.arena.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = MakeInt(f.arena, 3);
  range->index_end = MakeInt(f.arena, 7);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 5);
  inside->elements.push_back(range);

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideRangeNoMatch) {
  EvalOpFixture f;
  // 10 inside {[3:7]} = 0
  auto* range = f.arena.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = MakeInt(f.arena, 3);
  range->index_end = MakeInt(f.arena, 7);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 10);
  inside->elements.push_back(range);

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ==========================================================================
// Streaming concatenation ({<<{...}}, {>>{...}})
// ==========================================================================

TEST(EvalOp, StreamingLeftShift) {
  EvalOpFixture f;
  // {<<{8'hAB}} — reverse bit order of 0xAB
  auto* var = f.ctx.CreateVariable("sv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kLtLt;
  sc->elements.push_back(MakeId(f.arena, "sv"));

  auto result = EvalExpr(sc, f.ctx, f.arena);
  // 0xAB = 10101011 reversed = 11010101 = 0xD5
  EXPECT_EQ(result.ToUint64(), 0xD5u);
}

TEST(EvalOp, StreamingRightShift) {
  EvalOpFixture f;
  // {>>{8'hAB}} — same order (no reversal)
  auto* var = f.ctx.CreateVariable("sv2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kGtGt;
  sc->elements.push_back(MakeId(f.arena, "sv2"));

  auto result = EvalExpr(sc, f.ctx, f.arena);
  // Right-shift streaming: no bit reversal, just concatenate in order.
  EXPECT_EQ(result.ToUint64(), 0xABu);
}

// Helper: create a variable with specific aval/bval for a single word.
static Variable* MakeVar4(EvalOpFixture& f, std::string_view name,
                          uint32_t width, uint64_t aval, uint64_t bval) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}

// ==========================================================================
// Concatenation bval propagation — §11.4.12
// ==========================================================================

TEST(EvalOp, ConcatXZPropagation) {
  EvalOpFixture f;
  // {4'b1x0z, 4'b0101} = 8'b1x0z_0101
  // a = 4'b1x0z: aval=0b1001, bval=0b0101
  MakeVar4(f, "ca", 4, 0b1001, 0b0101);
  // b = 4'b0101: aval=0b0101, bval=0b0000
  auto* bv = f.ctx.CreateVariable("cb", 4);
  bv->value = MakeLogic4VecVal(f.arena, 4, 0b0101);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "ca"));
  concat->elements.push_back(MakeId(f.arena, "cb"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  // 8'b1x0z_0101:
  //   bit7=1, bit6=x, bit5=0, bit4=z, bit3=0, bit2=1, bit1=0, bit0=1
  //   aval: 1,0,0,1, 0,1,0,1 = 0b10010101 = 0x95
  //   bval: 0,1,0,1, 0,0,0,0 = 0b01010000 = 0x50
  EXPECT_EQ(result.words[0].aval, 0x95u);
  EXPECT_EQ(result.words[0].bval, 0x50u);
}

TEST(EvalOp, ReplicateXZPropagation) {
  EvalOpFixture f;
  // {2{4'b1x0z}} = 8'b1x0z_1x0z
  // 4'b1x0z: aval=0b1001, bval=0b0101
  MakeVar4(f, "rv", 4, 0b1001, 0b0101);

  auto* rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 2);
  rep->elements.push_back(MakeId(f.arena, "rv"));

  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  // 8'b1x0z_1x0z:
  //   aval: 1001_1001 = 0x99
  //   bval: 0101_0101 = 0x55
  EXPECT_EQ(result.words[0].aval, 0x99u);
  EXPECT_EQ(result.words[0].bval, 0x55u);
}

// ==========================================================================
// Additional edge cases
// ==========================================================================

TEST(EvalOp, ReductionAndZero) {
  EvalOpFixture f;
  // &32'd0 = 0
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, PercentEq) {
  EvalOpFixture f;
  auto* var = f.ctx.CreateVariable("m", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 17);

  auto* expr = MakeBinary(f.arena, TokenKind::kPercentEq, MakeId(f.arena, "m"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(EvalOp, CastShortint) {
  EvalOpFixture f;
  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "shortint";  // 16-bit type
  cast->lhs = MakeInt(f.arena, 0x1ABCD);

  auto result = EvalExpr(cast, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
  EXPECT_EQ(result.width, 16u);
}
