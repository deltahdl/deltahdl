// §11.4.8: Bitwise operators

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

namespace {

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

}  // namespace
