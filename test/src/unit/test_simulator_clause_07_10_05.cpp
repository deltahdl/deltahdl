#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

Expr* MakeConcat(Arena& arena, std::vector<Expr*> elems) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kConcatenation;
  e->elements = std::move(elems);
  return e;
}

// ---------------------------------------------------------------------------
// push_back on a full bounded queue
// ---------------------------------------------------------------------------

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

TEST(BoundedQueue, PushBackOnFullPreservesContents) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 30));
  q->AssignFreshIds();

  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 40)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(BoundedQueue, PushBackWarnsOnDiscard) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 2);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->AssignFreshIds();

  auto before = f.diag.WarningCount();
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 30)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

// ---------------------------------------------------------------------------
// push_front on a full bounded queue
// ---------------------------------------------------------------------------

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

TEST(BoundedQueue, PushFrontDiscardsLastElement) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 30));
  q->AssignFreshIds();

  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 5)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
}

TEST(BoundedQueue, PushFrontWarnsOnDiscard) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 2);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->AssignFreshIds();

  auto before = f.diag.WarningCount();
  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 5)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

// ---------------------------------------------------------------------------
// insert on a full bounded queue
// ---------------------------------------------------------------------------

TEST(BoundedQueue, InsertOnFullDiscardsLastElement) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 30));
  q->AssignFreshIds();

  auto* call =
      MakeMethodCall(f.arena, "q", "insert",
                     {MakeInt(f.arena, 1), MakeInt(f.arena, 15)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 15u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
}

TEST(BoundedQueue, InsertWarnsOnDiscard) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 2);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->AssignFreshIds();

  auto before = f.diag.WarningCount();
  auto* call =
      MakeMethodCall(f.arena, "q", "insert",
                     {MakeInt(f.arena, 1), MakeInt(f.arena, 15)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

// ---------------------------------------------------------------------------
// Indexed write Q[$+1] on a full bounded queue
// ---------------------------------------------------------------------------

TEST(BoundedQueue, IndexedWriteDollarPlusOneOnFullIsNoop) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 30));
  q->AssignFreshIds();

  auto* dollar = MakeId(f.arena, "$");
  auto* idx =
      MakeBinary(f.arena, TokenKind::kPlus, dollar, MakeInt(f.arena, 1));
  auto* lhs = MakeSelectExpr(f.arena, MakeId(f.arena, "q"), idx);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 40);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(BoundedQueue, IndexedWriteWarnsOnDiscard) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 2);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 20));
  q->AssignFreshIds();

  auto before = f.diag.WarningCount();
  auto* dollar = MakeId(f.arena, "$");
  auto* idx =
      MakeBinary(f.arena, TokenKind::kPlus, dollar, MakeInt(f.arena, 1));
  auto* lhs = MakeSelectExpr(f.arena, MakeId(f.arena, "q"), idx);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 30);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

// ---------------------------------------------------------------------------
// Queue assignment truncation
// ---------------------------------------------------------------------------

TEST(BoundedQueue, ConcatAssignTruncates) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements = {MakeLogic4VecVal(f.arena, 32, 10),
                 MakeLogic4VecVal(f.arena, 32, 20)};
  q->AssignFreshIds();
  // q = {q, 30, 40, 50} — would be 5 elements, bounded to 3.
  auto* rhs = MakeConcat(
      f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 30),
                MakeInt(f.arena, 40), MakeInt(f.arena, 50)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(BoundedQueue, ConcatAssignWarnsOnTruncate) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 2);
  q->elements = {MakeLogic4VecVal(f.arena, 32, 10)};
  q->AssignFreshIds();
  // q = {q, 20, 30} — would be 3 elements, bounded to 2.
  auto before = f.diag.WarningCount();
  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"),
                                   MakeInt(f.arena, 20),
                                   MakeInt(f.arena, 30)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

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

TEST(BoundedQueue, BoundOfOneAllowsSingleElement) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 1);

  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 42)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);

  auto* call2 =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 99)});
  TryExecQueueMethodStmt(call2, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

TEST(BoundedQueue, AssignWithinBoundNoWarning) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 5);
  q->AssignFreshIds();
  auto before = f.diag.WarningCount();
  // q = {1, 2, 3} — 3 elements, well within bound of 5.
  auto* rhs = MakeConcat(f.arena, {MakeInt(f.arena, 1), MakeInt(f.arena, 2),
                                   MakeInt(f.arena, 3)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(BoundedQueue, PushBackBelowBoundNoWarning) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 10));
  q->AssignFreshIds();

  auto before = f.diag.WarningCount();
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 20)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

}  // namespace
