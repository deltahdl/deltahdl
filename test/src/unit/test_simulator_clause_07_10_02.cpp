#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// --- §7.10.2 dispatch framework tests ---

TEST(QueueMethodDispatch, EvalReturnsFalseForNonQueueVariable) {
  SimFixture f;
  MakeVar(f, "x", 32, 42);
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "x", "size", {});
  EXPECT_FALSE(TryEvalQueueMethodCall(call, f.ctx, f.arena, out));
}

TEST(QueueMethodDispatch, ExecReturnsFalseForNonQueueVariable) {
  SimFixture f;
  MakeVar(f, "x", 32, 42);
  auto* call =
      MakeMethodCall(f.arena, "x", "push_back", {MakeInt(f.arena, 1)});
  EXPECT_FALSE(TryExecQueueMethodStmt(call, f.ctx, f.arena));
}

TEST(QueueMethodDispatch, EvalReturnsFalseForUnknownMethod) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "nonexistent", {});
  EXPECT_FALSE(TryEvalQueueMethodCall(call, f.ctx, f.arena, out));
}

TEST(QueueMethodDispatch, ExecReturnsFalseForUnknownMethod) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  auto* call = MakeMethodCall(f.arena, "q", "nonexistent", {});
  EXPECT_FALSE(TryExecQueueMethodStmt(call, f.ctx, f.arena));
}

TEST(QueueMethodDispatch, PropertyReturnsFalseForNonQueueVariable) {
  SimFixture f;
  MakeVar(f, "x", 32, 42);
  Logic4Vec out{};
  EXPECT_FALSE(TryEvalQueueProperty("x", "size", f.ctx, f.arena, out));
}

TEST(QueueMethodDispatch, PropertyReturnsFalseForUnknownProperty) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  Logic4Vec out{};
  EXPECT_FALSE(TryEvalQueueProperty("q", "nonexistent", f.ctx, f.arena, out));
}

}  // namespace
