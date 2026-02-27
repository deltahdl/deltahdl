// §11.4.11: Conditional operator


#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

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

namespace {

TEST(Eval, Ternary) {
  ExprFixture f;
  auto* expr = ParseExprFrom("1 ? 42 : 99", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

}  // namespace
