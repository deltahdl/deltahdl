// §11.4.13: for an explanation of range list syntax.

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

static Expr* ParseExprFrom(const std::string& src, AggFixture& f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  auto* item = cu->modules[0]->items[0];
  return item->body->rhs;
}

namespace {

// =============================================================================
// §11.2.2 Aggregate expressions — struct in set membership
// =============================================================================
TEST(AggregateExpr, PackedStructInsideSet) {
  // A packed struct is just a bitvector — inside should work by value.
  AggFixture f;
  auto* var = f.ctx.CreateVariable("s", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 5);
  auto* expr = ParseExprFrom("s inside {5, 10, 15}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(AggregateExpr, PackedStructNotInSet) {
  AggFixture f;
  auto* var = f.ctx.CreateVariable("s", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 7);
  auto* expr = ParseExprFrom("s inside {5, 10, 15}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
