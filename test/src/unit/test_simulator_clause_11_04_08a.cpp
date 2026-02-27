// §11.4.8: Bitwise operators


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

TEST(Eval, BitwiseAnd) {
  ExprFixture f;
  auto* expr = ParseExprFrom("15 & 6", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 6u);
}

}  // namespace
