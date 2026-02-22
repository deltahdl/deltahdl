// §10.9: Assignment patterns

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
struct AggFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *ParseExprFrom(const std::string &src, AggFixture &f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  auto *item = cu->modules[0]->items[0];
  return item->body->rhs;
}

namespace {

// =============================================================================
// §10.9 Assignment pattern evaluation
// =============================================================================
TEST(AssignmentPattern, PositionalTwoElements) {
  // '{a, b} with 8-bit variables → 16-bit packed result
  AggFixture f;
  auto *a = f.ctx.CreateVariable("a", 8);
  auto *b = f.ctx.CreateVariable("b", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 5);
  b->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto *expr = ParseExprFrom("'{a, b}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // {a=5, b=10} → MSB-first: 5 in [15:8], 10 in [7:0] = 16'h050A
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(AssignmentPattern, PositionalThreeElements) {
  AggFixture f;
  auto *a = f.ctx.CreateVariable("a", 4);
  auto *b = f.ctx.CreateVariable("b", 4);
  auto *c = f.ctx.CreateVariable("c", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 1);
  b->value = MakeLogic4VecVal(f.arena, 4, 2);
  c->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto *expr = ParseExprFrom("'{a, b, c}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // {1, 2, 3} → 12-bit: 0x123
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0x123u);
}

TEST(AssignmentPattern, SingleElement) {
  AggFixture f;
  auto *a = f.ctx.CreateVariable("a", 32);
  a->value = MakeLogic4VecVal(f.arena, 32, 42);
  auto *expr = ParseExprFrom("'{a}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(AssignmentPattern, EmptyPattern) {
  AggFixture f;
  auto *expr = ParseExprFrom("'{}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 0u);
}

TEST(AssignmentPattern, SizedLiterals) {
  // Test the parser fix for integer literal first elements
  AggFixture f;
  auto *expr = ParseExprFrom("'{32'd5, 32'd10}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Both are 32-bit (evaluator returns 32-bit for all int literals)
  // {32'd5, 32'd10} → 64-bit: upper=5, lower=10
  EXPECT_EQ(result.width, 64u);
  uint64_t expected = (uint64_t{5} << 32) | 10;
  EXPECT_EQ(result.ToUint64(), expected);
}

}  // namespace
