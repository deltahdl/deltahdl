#include <gtest/gtest.h>

#include <cstring>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

// Shared fixture for advanced expression evaluation tests (§11 phases 22+).
struct EvalAdvFixture {
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

static Variable* MakeVar(EvalAdvFixture& f, std::string_view name,
                         uint32_t width, uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  return var;
}

// ==========================================================================
// §11.4.14: Streaming operator — basic integral test (existing behavior)
// ==========================================================================

TEST(EvalAdv, StreamingLeftShiftReversesSlices) {
  EvalAdvFixture f;
  // {<< 8 {16'hABCD}} → reverse 8-bit slices: 0xCDAB
  MakeVar(f, "sv", 16, 0xABCD);
  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kLtLt;
  auto* size_expr = f.arena.Create<Expr>();
  size_expr->kind = ExprKind::kIntegerLiteral;
  size_expr->text = "8";
  size_expr->int_val = 8;
  stream->lhs = size_expr;
  stream->elements.push_back(MakeId(f.arena, "sv"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xCDABu);
}

TEST(EvalAdv, StreamingRightShiftPreservesOrder) {
  EvalAdvFixture f;
  // {>> 8 {16'hABCD}} → no reversal, same as concat.
  MakeVar(f, "sv2", 16, 0xABCD);
  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  auto* size_expr = f.arena.Create<Expr>();
  size_expr->kind = ExprKind::kIntegerLiteral;
  size_expr->text = "8";
  size_expr->int_val = 8;
  stream->lhs = size_expr;
  stream->elements.push_back(MakeId(f.arena, "sv2"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
}

// ==========================================================================
// §11.4.14.1: Streaming with unpacked array — element concatenation
// ==========================================================================

TEST(EvalAdv, StreamingUnpackedArrayConcat) {
  EvalAdvFixture f;
  // Create unpacked array: arr[0]=0xAB, arr[1]=0xCD, each 8-bit.
  MakeVar(f, "arr[0]", 8, 0xAB);
  MakeVar(f, "arr[1]", 8, 0xCD);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr", info);

  // {>> {arr}} → right-shift stream: concatenate MSB-first = 0xABCD.
  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "arr"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
}

TEST(EvalAdv, StreamingUnpackedArrayLeftShift) {
  EvalAdvFixture f;
  // Create unpacked array: arr2[0]=0xAB, arr2[1]=0xCD.
  MakeVar(f, "arr2[0]", 8, 0xAB);
  MakeVar(f, "arr2[1]", 8, 0xCD);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr2", info);

  // {<< 8 {arr2}} → left-shift stream with 8-bit slices: reversal = 0xCDAB.
  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kLtLt;
  auto* size_expr = f.arena.Create<Expr>();
  size_expr->kind = ExprKind::kIntegerLiteral;
  size_expr->text = "8";
  size_expr->int_val = 8;
  stream->lhs = size_expr;
  stream->elements.push_back(MakeId(f.arena, "arr2"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xCDABu);
}

TEST(EvalAdv, StreamingUnpackedArrayMissingElemGivesX) {
  EvalAdvFixture f;
  // Array with 3 elements but only [0] and [2] exist — [1] should be X.
  MakeVar(f, "arr3[0]", 8, 0x11);
  MakeVar(f, "arr3[2]", 8, 0x33);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 3;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr3", info);

  auto* stream = f.arena.Create<Expr>();
  stream->kind = ExprKind::kStreamingConcat;
  stream->op = TokenKind::kGtGt;
  stream->elements.push_back(MakeId(f.arena, "arr3"));
  auto result = EvalExpr(stream, f.ctx, f.arena);
  EXPECT_EQ(result.width, 24u);
  // arr3[0]=0x11, arr3[1]=X(0x00), arr3[2]=0x33 → 0x110033
  EXPECT_EQ(result.ToUint64(), 0x110033u);
}

// ==========================================================================
// §11.2.2: Aggregate expressions — struct equality
// ==========================================================================

// NOTE: Struct aggregate equality requires struct type infrastructure.
// Placeholder tests validate the existing TryArrayEqualityOp path.

// ==========================================================================
// §11.9: Tagged union — tag mismatch returns X
// ==========================================================================

TEST(EvalAdv, TaggedUnionMismatchReturnsX) {
  EvalAdvFixture f;
  // Create a tagged union type with members a (8-bit) and b (8-bit).
  StructTypeInfo uinfo;
  uinfo.type_name = "tagged_u";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("tagged_u", uinfo);

  // Create variable "u" with value 0x42 and tag "a".
  MakeVar(f, "u", 8, 0x42);
  f.ctx.SetVariableStructType("u", "tagged_u");
  f.ctx.SetVariableTag("u", "a");

  // Access u.a — tag matches, should return 0x42.
  auto* access_a = f.arena.Create<Expr>();
  access_a->kind = ExprKind::kMemberAccess;
  access_a->lhs = MakeId(f.arena, "u");
  access_a->rhs = MakeId(f.arena, "a");
  auto result_a = EvalExpr(access_a, f.ctx, f.arena);
  EXPECT_EQ(result_a.ToUint64(), 0x42u);

  // Access u.b — tag mismatch (active tag is "a"), should return X.
  auto* access_b = f.arena.Create<Expr>();
  access_b->kind = ExprKind::kMemberAccess;
  access_b->lhs = MakeId(f.arena, "u");
  access_b->rhs = MakeId(f.arena, "b");
  auto result_b = EvalExpr(access_b, f.ctx, f.arena);
  // X means bval all-1s.
  EXPECT_NE(result_b.nwords, 0u);
  EXPECT_NE(result_b.words[0].bval, 0u);
}

TEST(EvalAdv, TaggedUnionNoTagSetAccessesNormally) {
  EvalAdvFixture f;
  // Union without a tag set should still allow access.
  StructTypeInfo uinfo;
  uinfo.type_name = "simple_u";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"x", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("simple_u", uinfo);

  MakeVar(f, "v", 8, 0xFF);
  f.ctx.SetVariableStructType("v", "simple_u");
  // No tag set — access v.x should return the value normally.
  auto* access_x = f.arena.Create<Expr>();
  access_x->kind = ExprKind::kMemberAccess;
  access_x->lhs = MakeId(f.arena, "v");
  access_x->rhs = MakeId(f.arena, "x");
  auto result_x = EvalExpr(access_x, f.ctx, f.arena);
  EXPECT_EQ(result_x.ToUint64(), 0xFFu);
}

// ==========================================================================
// §11.3.6: Assignment within expression
// ==========================================================================

TEST(EvalAdv, AssignInExprBasic) {
  EvalAdvFixture f;
  // (a = 42) should assign 42 to a and return 42.
  MakeVar(f, "aie", 32, 0);
  auto* assign = f.arena.Create<Expr>();
  assign->kind = ExprKind::kBinary;
  assign->op = TokenKind::kEq;
  assign->lhs = MakeId(f.arena, "aie");
  assign->rhs = MakeInt(f.arena, 42);
  auto result = EvalExpr(assign, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  auto* var = f.ctx.FindVariable("aie");
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(EvalAdv, AssignInExprTruncToLHSWidth) {
  EvalAdvFixture f;
  // (b = 0x1FF) where b is 8-bit should truncate to 0xFF.
  MakeVar(f, "aie8", 8, 0);
  auto* assign = f.arena.Create<Expr>();
  assign->kind = ExprKind::kBinary;
  assign->op = TokenKind::kEq;
  assign->lhs = MakeId(f.arena, "aie8");
  assign->rhs = MakeInt(f.arena, 0x1FF);
  auto result = EvalExpr(assign, f.ctx, f.arena);
  // §11.3.6: Result should be cast to LHS type (8-bit).
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

// ==========================================================================
// §11.2.2: Aggregate expressions — packed struct equality
// ==========================================================================

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

TEST(EvalAdv, PackedStructEqualitySameValue) {
  EvalAdvFixture f;
  // Two 16-bit packed struct vars with same value → == is 1.
  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s1", 16, 0xABCD);
  MakeVar(f, "s2", 16, 0xABCD);
  f.ctx.SetVariableStructType("s1", "my_struct");
  f.ctx.SetVariableStructType("s2", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "s1"),
                          MakeId(f.arena, "s2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, PackedStructEqualityDiffValue) {
  EvalAdvFixture f;
  // Two 16-bit packed struct vars with different values → == is 0.
  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s3", 16, 0xABCD);
  MakeVar(f, "s4", 16, 0x1234);
  f.ctx.SetVariableStructType("s3", "my_struct");
  f.ctx.SetVariableStructType("s4", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "s3"),
                          MakeId(f.arena, "s4"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, PackedStructInequality) {
  EvalAdvFixture f;
  StructTypeInfo sinfo;
  sinfo.type_name = "my_struct";
  sinfo.total_width = 16;
  sinfo.is_packed = true;
  sinfo.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  sinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("my_struct", sinfo);
  MakeVar(f, "s5", 16, 0xABCD);
  MakeVar(f, "s6", 16, 0x1234);
  f.ctx.SetVariableStructType("s5", "my_struct");
  f.ctx.SetVariableStructType("s6", "my_struct");
  auto* expr = MakeBinary(f.arena, TokenKind::kBangEq, MakeId(f.arena, "s5"),
                          MakeId(f.arena, "s6"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// ==========================================================================
// §11.9: Tagged union expressions
// ==========================================================================

TEST(EvalAdv, TaggedExprWithValue) {
  EvalAdvFixture f;
  // tagged Valid 42 → evaluates to 42.
  auto* tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Valid";
  tagged->rhs = member;
  tagged->lhs = MakeInt(f.arena, 42);
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(EvalAdv, TaggedExprVoidMember) {
  EvalAdvFixture f;
  // tagged Invalid (void member, no value) → 0.
  auto* tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Invalid";
  tagged->rhs = member;
  tagged->lhs = nullptr;
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ==========================================================================
// Inside operator advanced features — §11.4.13
// ==========================================================================

static Expr* MakeRange(Arena& arena, Expr* lo, Expr* hi,
                       TokenKind op = TokenKind::kEof) {
  auto* r = arena.Create<Expr>();
  r->kind = ExprKind::kSelect;
  r->index = lo;
  r->index_end = hi;
  r->op = op;
  return r;
}

static Expr* MakeDollar(Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = "$";
  return e;
}

TEST(EvalAdv, InsideDollarLowerBound) {
  EvalAdvFixture f;
  auto* var = f.ctx.CreateVariable("dv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "dv");
  inside->elements.push_back(
      MakeRange(f.arena, MakeDollar(f.arena), MakeInt(f.arena, 10)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideDollarUpperBound) {
  EvalAdvFixture f;
  auto* var = f.ctx.CreateVariable("du", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 200);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "du");
  inside->elements.push_back(
      MakeRange(f.arena, MakeInt(f.arena, 100), MakeDollar(f.arena)));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideAbsTolerance) {
  EvalAdvFixture f;
  auto* var = f.ctx.CreateVariable("at", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "at");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 5),
                                       TokenKind::kPlusSlashMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideAbsToleranceMiss) {
  EvalAdvFixture f;
  auto* var = f.ctx.CreateVariable("am", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 20);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "am");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 5),
                                       TokenKind::kPlusSlashMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, InsideRelTolerance) {
  EvalAdvFixture f;
  auto* var = f.ctx.CreateVariable("rt", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 8);
  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "rt");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 10),
                                       MakeInt(f.arena, 25),
                                       TokenKind::kPlusPercentMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// ==========================================================================
// Power operator edge cases — §11.4.3, Table 11-4
// ==========================================================================

static Variable* MakeSignedVarAdv(EvalAdvFixture& f, std::string_view name,
                                  uint32_t width, uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  var->is_signed = true;
  return var;
}

TEST(EvalAdv, PowZeroExp) {
  EvalAdvFixture f;
  // a ** 0 = 1 for any a (Table 11-4).
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeInt(f.arena, 7);
  expr->rhs = MakeInt(f.arena, 0);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, PowNegExpInt) {
  EvalAdvFixture f;
  // 3 ** (-2) = 0 for integer (Table 11-4: |base|>1, negative exp → 0).
  MakeSignedVarAdv(f, "pb", 8, 3);
  // -2 in 8-bit signed = 0xFE
  MakeSignedVarAdv(f, "pe", 8, 0xFE);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "pb");
  expr->rhs = MakeId(f.arena, "pe");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, PowZeroBaseNegExp) {
  EvalAdvFixture f;
  // 0 ** (-1) = X (Table 11-4: zero base, negative exp → X).
  MakeSignedVarAdv(f, "zb", 8, 0);
  MakeSignedVarAdv(f, "ze", 8, 0xFF);  // -1 in 8-bit
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "zb");
  expr->rhs = MakeId(f.arena, "ze");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

TEST(EvalAdv, PowNeg1OddExp) {
  EvalAdvFixture f;
  // (-1) ** 3 = -1 (Table 11-4: base -1, odd exp).
  MakeSignedVarAdv(f, "n1", 8, 0xFF);  // -1 in 8-bit
  MakeSignedVarAdv(f, "n3", 8, 3);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1");
  expr->rhs = MakeId(f.arena, "n3");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);  // -1 in 8-bit
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, PowNeg1EvenExp) {
  EvalAdvFixture f;
  // (-1) ** 4 = 1 (Table 11-4: base -1, even exp).
  MakeSignedVarAdv(f, "n1", 8, 0xFF);  // -1 in 8-bit
  MakeSignedVarAdv(f, "n4", 8, 4);
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kPower;
  expr->lhs = MakeId(f.arena, "n1");
  expr->rhs = MakeId(f.arena, "n4");
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_TRUE(result.is_signed);
}

// ==========================================================================
// Signed comparison — §11.4.4, §11.4.5, §11.8.1
// ==========================================================================

TEST(EvalAdv, SignedLtNeg) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeSignedVarAdv(f, "sb", 8, 0x01);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, SignedGtNeg) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0x01);
  MakeSignedVarAdv(f, "sb", 8, 0xFF);
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, SignedEqNeg) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeSignedVarAdv(f, "sb", 8, 0xFF);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, UnsignedLtUnchanged) {
  EvalAdvFixture f;
  auto* a = MakeVar(f, "ua", 8, 0xFF);
  (void)a;
  auto* b = MakeVar(f, "ub", 8, 0x01);
  (void)b;
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "ua"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// ==========================================================================
// Signed arithmetic — §11.4.3, §11.4.3.1
// ==========================================================================

TEST(EvalAdv, SignedDivTruncToZero) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "sd", 8, 0xF9);
  MakeSignedVarAdv(f, "se", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "sd"),
                          MakeId(f.arena, "se"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFDu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, SignedModSignOfFirst) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "sm", 8, 0xF9);
  MakeSignedVarAdv(f, "sn", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "sm"),
                          MakeId(f.arena, "sn"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xFFu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, SignedMulNeg) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "ma", 8, 0xFD);
  MakeSignedVarAdv(f, "mb", 8, 4);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "ma"),
                          MakeId(f.arena, "mb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64() & 0xFF, 0xF4u);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, UnsignedDivUnchanged) {
  EvalAdvFixture f;
  auto* a = MakeVar(f, "ud", 8, 0xF9);
  (void)a;
  auto* b = MakeVar(f, "ue", 8, 2);
  (void)b;
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "ud"),
                          MakeId(f.arena, "ue"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 124u);
}

// ==========================================================================
// Expression type rules — §11.8.1
// ==========================================================================

TEST(EvalAdv, ComparisonResultUnsigned) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "ca", 8, 1);
  MakeSignedVarAdv(f, "cb", 8, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "ca"),
                          MakeId(f.arena, "cb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, ReductionResultUnsigned) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "rv", 8, 0xFF);
  auto* expr = MakeUnary(f.arena, TokenKind::kAmp, MakeId(f.arena, "rv"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, ConcatResultUnsigned) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "c1", 4, 0xA);
  MakeSignedVarAdv(f, "c2", 4, 0xB);
  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "c1"));
  concat->elements.push_back(MakeId(f.arena, "c2"));
  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xABu);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, BitwiseSignedResult) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "b1", 8, 0xFF);
  MakeSignedVarAdv(f, "b2", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kAmp, MakeId(f.arena, "b1"),
                          MakeId(f.arena, "b2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0Fu);
  EXPECT_TRUE(result.is_signed);
}

TEST(EvalAdv, MixedSignUnsignedResult) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "ms", 8, 0xFF);
  auto* u = MakeVar(f, "mu", 8, 0x0F);
  (void)u;
  auto* expr = MakeBinary(f.arena, TokenKind::kAmp, MakeId(f.arena, "ms"),
                          MakeId(f.arena, "mu"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, BitSelectUnsigned) {
  EvalAdvFixture f;
  // §11.8.1: Bit-select result is always unsigned.
  MakeSignedVarAdv(f, "bs", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bs");
  sel->index = MakeInt(f.arena, 3);
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_FALSE(result.is_signed);
}

TEST(EvalAdv, PartSelectUnsigned) {
  EvalAdvFixture f;
  // §11.8.1: Part-select result is always unsigned.
  MakeSignedVarAdv(f, "ps", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ps");
  sel->index = MakeInt(f.arena, 0);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 0xFu);
  EXPECT_FALSE(result.is_signed);
}

static Variable* MakeVar4Adv(EvalAdvFixture& f, std::string_view name,
                              uint32_t width, uint64_t aval, uint64_t bval) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}

TEST(EvalAdv, SignedXFillsX) {
  EvalAdvFixture f;
  // §11.8.4: Sign bit X → fill with X during sign extension.
  // 4-bit signed value with sign bit (bit3) = X: aval=0b0001, bval=0b1000
  auto* var = MakeVar4Adv(f, "sx", 4, 0b0001, 0b1000);
  var->is_signed = true;
  // Use $signed to trigger sign extension to 8-bit context.
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sx"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);
  // With sign bit X, upper bits should be X (bval set).
  EXPECT_NE(result.words[0].bval & 0xF0u, 0u);
}

TEST(EvalAdv, SignedZFillsZ) {
  EvalAdvFixture f;
  // §11.8.4: Sign bit Z → fill with Z during sign extension.
  // Z encoding: aval=0, bval=1 for sign bit (bit3).
  auto* var = MakeVar4Adv(f, "sz", 4, 0b0001, 0b1000);
  var->is_signed = true;
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sz"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);
  // With sign bit X/Z, upper bits should have bval set.
  EXPECT_NE(result.words[0].bval & 0xF0u, 0u);
}

// ==========================================================================
// Part-select partial OOB — §11.5.1
// ==========================================================================

TEST(EvalAdv, PartSelectPartialOOB) {
  EvalAdvFixture f;
  // §11.5.1: v[6 +: 4] on 8-bit var → bits 6,7 valid, bits 8,9 OOB → X.
  MakeVar(f, "ov", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ov");
  sel->index = MakeInt(f.arena, 6);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  // Bits 0,1 (= original bits 6,7) should be 1 (known).
  EXPECT_EQ(result.words[0].aval & 0x3u, 0x3u);
  // Bits 2,3 (= original bits 8,9) should be X (bval set).
  EXPECT_NE(result.words[0].bval & 0xCu, 0u);
}

// ==========================================================================
// Real increment/decrement — §11.4.2
// ==========================================================================

static Variable* MakeRealVarAdv(EvalAdvFixture& f, std::string_view name,
                                double val) {
  auto* var = f.ctx.CreateVariable(name, 64);
  uint64_t bits = 0;
  std::memcpy(&bits, &val, sizeof(double));
  var->value = MakeLogic4VecVal(f.arena, 64, bits);
  var->value.is_real = true;
  f.ctx.RegisterRealVariable(name);
  return var;
}

static double AdvToDouble(const Logic4Vec& v) {
  double d = 0.0;
  uint64_t bits = v.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

TEST(EvalAdv, RealIncrementBy1Point0) {
  EvalAdvFixture f;
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

// ==========================================================================
// §11.3.3: Signed-base literal is_signed flag
// ==========================================================================

// Helper: build a sized literal with text (for base detection).
static Expr* MakeSizedLiteral(Arena& arena, std::string_view text,
                              uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->text = text;
  e->int_val = val;
  return e;
}

TEST(EvalAdv, SignedBaseLiteralIsSigned) {
  EvalAdvFixture f;
  // §11.3.3: 4'sd3 should produce is_signed=true on the Logic4Vec.
  auto* lit = MakeSizedLiteral(f.arena, "4'sd3", 3);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(EvalAdv, UnsignedBaseLiteralNotSigned) {
  EvalAdvFixture f;
  // 4'd3 should produce is_signed=false.
  auto* lit = MakeSizedLiteral(f.arena, "4'd3", 3);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(EvalAdv, SignedHexLiteralIsSigned) {
  EvalAdvFixture f;
  // 8'shFF should produce is_signed=true.
  auto* lit = MakeSizedLiteral(f.arena, "8'shFF", 0xFF);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

// ==========================================================================
// §11.12: Let construct expansion (§F.4)
// ==========================================================================

// Helper: build a let declaration ModuleItem.
static ModuleItem* MakeLetDecl(Arena& arena, std::string_view name, Expr* body,
                               std::vector<FunctionArg> args = {}) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kLetDecl;
  item->name = name;
  item->init_expr = body;
  item->func_args = std::move(args);
  return item;
}

// Helper: build a function call expression (used for let instantiation).
static Expr* MakeCall(Arena& arena, std::string_view callee,
                      std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->callee = callee;
  e->args = std::move(args);
  return e;
}

TEST(EvalAdv, LetExpandSimple) {
  EvalAdvFixture f;
  // let add1(a) = a + 1;
  FunctionArg arg;
  arg.name = "a";
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  body->rhs = MakeInt(f.arena, 1);
  auto* decl = MakeLetDecl(f.arena, "add1", body, {arg});
  f.ctx.RegisterLetDecl("add1", decl);

  // add1(5) should return 6.
  auto* call = MakeCall(f.arena, "add1", {MakeInt(f.arena, 5)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 6u);
}

TEST(EvalAdv, LetExpandDefaultArg) {
  EvalAdvFixture f;
  // let inc(a, b = 1) = a + b;
  FunctionArg arg_a;
  arg_a.name = "a";
  FunctionArg arg_b;
  arg_b.name = "b";
  arg_b.default_value = MakeInt(f.arena, 1);
  auto* body = f.arena.Create<Expr>();
  body->kind = ExprKind::kBinary;
  body->op = TokenKind::kPlus;
  body->lhs = MakeId(f.arena, "a");
  body->rhs = MakeId(f.arena, "b");
  auto* decl = MakeLetDecl(f.arena, "inc", body, {arg_a, arg_b});
  f.ctx.RegisterLetDecl("inc", decl);

  // inc(10) — uses default b=1, should return 11.
  auto* call = MakeCall(f.arena, "inc", {MakeInt(f.arena, 10)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 11u);
}
