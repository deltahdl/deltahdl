// §13.3: Tasks

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>
#include <string>

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

// =============================================================================
// Phase 6: §13 Task call setup/teardown
// =============================================================================
TEST(TaskCall, SetupReturnsTaskItem) {
  AggFixture f;
  // Create a task declaration node.
  auto *task = f.arena.Create<ModuleItem>();
  task->kind = ModuleItemKind::kTaskDecl;
  task->name = "my_task";
  f.ctx.RegisterFunction("my_task", task);

  // Build a kCall expression targeting the task.
  auto *call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "my_task";

  auto *result = SetupTaskCall(call, f.ctx, f.arena);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->name, "my_task");
  // Clean up scope pushed by SetupTaskCall.
  TeardownTaskCall(result, call, f.ctx);
}

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

TEST(TaskCall, SetupReturnsNullForUnknown) {
  AggFixture f;
  auto *call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "nonexistent";

  auto *result = SetupTaskCall(call, f.ctx, f.arena);
  EXPECT_EQ(result, nullptr);
}

} // namespace
