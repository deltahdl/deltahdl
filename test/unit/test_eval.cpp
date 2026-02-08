#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

struct ExprFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler;
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr* ParseExprFrom(const std::string& src, ExprFixture& f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  // Extract the RHS of the blocking assignment in the initial block.
  auto* item = cu->modules[0]->items[0];
  return item->body->rhs;
}

TEST(Eval, IntegerLiteral) {
  ExprFixture f;
  auto* expr = ParseExprFrom("42", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(Eval, Addition) {
  ExprFixture f;
  auto* expr = ParseExprFrom("10 + 32", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(Eval, BitwiseAnd) {
  ExprFixture f;
  auto* expr = ParseExprFrom("15 & 6", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 6u);
}

TEST(Eval, Comparison) {
  ExprFixture f;
  auto* expr = ParseExprFrom("5 > 3", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(Eval, Ternary) {
  ExprFixture f;
  auto* expr = ParseExprFrom("1 ? 42 : 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(Eval, VariableLookup) {
  ExprFixture f;
  auto* var = f.ctx.CreateVariable("myvar", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 123);

  // Create an identifier expression manually.
  auto* expr = f.arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "myvar";
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 123u);
}
