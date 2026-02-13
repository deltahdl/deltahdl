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
// §11.2.2: Aggregate expressions — struct equality
// ==========================================================================

// NOTE: Struct aggregate equality requires struct type infrastructure.
// Placeholder tests validate the existing TryArrayEqualityOp path.

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
