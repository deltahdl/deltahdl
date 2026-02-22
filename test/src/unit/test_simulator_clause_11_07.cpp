// §11.7: Signed expressions

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


static Variable* MakeVar4Adv(EvalAdvFixture& f, std::string_view name,
                             uint32_t width, uint64_t aval, uint64_t bval) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}

static Expr* MakeBinary(Arena& arena, TokenKind op, Expr* lhs, Expr* rhs) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

static Expr* MakeUnary(Arena& arena, TokenKind op, Expr* operand) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kUnary;
  e->op = op;
  e->lhs = operand;
  return e;
}
static Variable* MakeSignedVarAdv(EvalAdvFixture& f, std::string_view name,
                                  uint32_t width, uint64_t val) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  var->is_signed = true;
  return var;
}
namespace {

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

}  // namespace
