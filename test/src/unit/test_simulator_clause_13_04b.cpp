// §13.4: Functions

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

namespace {

TEST(TaskCall, SetupReturnsNullForFunction) {
  AggFixture f;
  // Create a function (not task) declaration.
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "my_func";
  f.ctx.RegisterFunction("my_func", func);

  auto *call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "my_func";

  auto *result = SetupTaskCall(call, f.ctx, f.arena);
  EXPECT_EQ(result, nullptr);
}

}  // namespace
