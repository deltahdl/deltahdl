// §10.9.1: Array assignment patterns

#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
static Expr* ParseExprFrom(const std::string& src, SimFixture& f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  auto* item = cu->modules[0]->items[0];
  return item->body->rhs;
}

namespace {

TEST(AssignmentPattern, PositionalThreeElements) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("a", 4);
  auto* b = f.ctx.CreateVariable("b", 4);
  auto* c = f.ctx.CreateVariable("c", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 1);
  b->value = MakeLogic4VecVal(f.arena, 4, 2);
  c->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = ParseExprFrom("'{a, b, c}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // {1, 2, 3} → 12-bit: 0x123
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0x123u);
}

}  // namespace
