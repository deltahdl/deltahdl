#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/eval_array.h"

using namespace delta;

namespace {

TEST(BoundedQueue, PushBackRespectsMax) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 30));
  q->AssignFreshIds();

  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 40)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
}

TEST(BoundedQueue, PushFrontRespectsMax) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 30));
  q->AssignFreshIds();

  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 5)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
}

TEST(BoundedQueue, AllowsPushAfterDelete) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 30));
  q->AssignFreshIds();

  auto* del = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 0)});
  TryExecQueueMethodStmt(del, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);

  auto* push =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 40)});
  TryExecQueueMethodStmt(push, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 40u);
}

TEST(BoundedQueue, UnboundedHasNoLimit) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  for (int i = 0; i < 100; ++i) {
    auto* call = MakeMethodCall(f.arena, "q", "push_back",
                                {MakeInt(f.arena, static_cast<uint64_t>(i))});
    TryExecQueueMethodStmt(call, f.ctx, f.arena);
  }
  EXPECT_EQ(q->elements.size(), 100u);
}

}
