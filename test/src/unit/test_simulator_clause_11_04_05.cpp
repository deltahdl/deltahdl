// §11.4.5: Equality operators

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

namespace {

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

}  // namespace
