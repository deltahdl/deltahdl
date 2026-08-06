// Tests for §7.10.3 "Persistence of references to elements of a queue".
//
// §7.10.3 specifies *which* queue operations cause an outstanding reference to
// a queue element to become outdated (the meaning of "outdated" itself is owned
// by §13.5.2, a dependency). It states two normative rules of its own:
//
//   Rule A - When a queue method (§7.10.2) updates a queue, a reference to any
//            element the method does not remove stays valid; references to any
//            element the method removes become outdated.
//   Rule B - When the target of an assignment is an entire queue, references to
//            every element of the original queue become outdated.
//
// All of this is a simulator-stage concern. A queue element passed by reference
// is recorded by element id (eval_function.cpp RecordQueueRef); on return the
// writeback (WritebackQueueRefs) only stores back when that id is still present
// in the queue. A surviving element keeps its id, so the write lands; a removed
// element's id is gone, so the write is dropped - that dropped write is how an
// outdated reference is observed here. Per-method id maintenance lives in
// eval_array.cpp; whole-queue assignment discarding all ids lives in
// statement_assign.cpp / statement_assign_core.cpp.

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Build an automatic function taking one ref arg `v` that performs `op` on the
// queue and then writes 99 through the reference. If the reference is outdated
// by `op`, the write is dropped and the queue keeps its pre-write contents.
void RunRefOpThenWrite(SimFixture& f, std::vector<Stmt*> op_stmts,
                       Expr* ref_arg) {
  op_stmts.push_back(MakeAssign(f.arena, "v", MakeInt(f.arena, 99)));
  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              std::move(op_stmts));
  auto* call = MakeCall(f.arena, "test_fn", {ref_arg});
  EvalExpr(call, f.ctx, f.arena);
}

// Shared body for the "front-prepending op never outdates an existing ref"
// cases (insert at 0 and push_front), which prepend `5` to {10,20,30} and hold
// a reference to original element 20 at its new index 2. The op leaves the
// reference valid, so the write of 99 lands there, yielding {5,10,99,30}.
void ExpectPrependKeepsRefValid(SimFixture& f, Stmt* op_stmt) {
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(f, {op_stmt}, MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);  // original element 20 survived
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

// --- Rule A: methods outdate only the elements they remove
// --------------------

// delete(idx) removes the indexed element, so a reference held to it is
// outdated and the later write through that reference is dropped.
TEST(QueueRefPersistence, DeleteOutdatesRemovedElementRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete",
                                            {MakeInt(f.arena, 1)}))},
      MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);  // no 99: the ref was outdated
}

// A reference to an element the method does not delete must survive: the write
// lands on that element at its new position.
TEST(QueueRefPersistence, DeleteLeavesOtherElementRefValid) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete",
                                            {MakeInt(f.arena, 1)}))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 99u);  // survived: write applied
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

// delete() with no index removes every element, so per Rule A every outstanding
// reference is to a removed element and all become outdated; the write through
// the held reference is dropped and the queue stays empty.
TEST(QueueRefPersistence, DeleteAllOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete", {}))},
      MakeSelect(f.arena, "q", 1));

  EXPECT_EQ(q->elements.size(),
            0u);  // all removed: ref outdated, write dropped
}

// pop_front removes the first element, outdating a reference to it.
TEST(QueueRefPersistence, PopFrontOutdatesPoppedElementRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_front", {}))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

// pop_front leaves a reference to a non-popped element valid.
TEST(QueueRefPersistence, PopFrontLeavesRemainingRefValid) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_front", {}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);  // element 30 survived under id
}

// pop_back removes the last element, outdating a reference to it.
TEST(QueueRefPersistence, PopBackOutdatesPoppedElementRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_back", {}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// pop_back removes only the last element, so a reference to any earlier element
// is not outdated and its write lands.
TEST(QueueRefPersistence, PopBackLeavesRemainingRefValid) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_back", {}))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 99u);  // element 10 survived under id
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// insert adds an element without removing any existing one, so an existing
// reference can never be outdated; the write lands at the element's new index.
TEST(QueueRefPersistence, InsertNeverOutdatesExistingRef) {
  SimFixture f;
  ExpectPrependKeepsRefValid(
      f, MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "insert",
                                              {MakeInt(f.arena, 0),
                                               MakeInt(f.arena, 5)})));
}

// push_back never outdates an existing reference.
TEST(QueueRefPersistence, PushBackNeverOutdatesExistingRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                            {MakeInt(f.arena, 40)}))},
      MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

// push_front never outdates an existing reference.
TEST(QueueRefPersistence, PushFrontNeverOutdatesExistingRef) {
  SimFixture f;
  ExpectPrependKeepsRefValid(
      f, MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_front",
                                              {MakeInt(f.arena, 5)})));
}

// Consequence noted in §7.10.3: insert/push_front on a *bounded* queue whose
// new size would exceed the bound deletes the highest-numbered element, so a
// reference held to that dropped tail element becomes outdated.
TEST(QueueRefPersistence, BoundedInsertOutdatesDroppedTailRef) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  for (auto v : {10u, 20u, 30u})
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  q->AssignFreshIds();

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(
          f.arena, MakeMethodCall(f.arena, "q", "insert",
                                  {MakeInt(f.arena, 0), MakeInt(f.arena, 5)}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);  // dropped tail (30) ref outdated
}

// The same consequence names push_front explicitly: a push_front that pushes a
// bounded queue past its bound drops the highest-numbered element, so a
// reference held to that dropped tail element becomes outdated. This exercises
// the push_front overflow path, distinct from the insert path above.
TEST(QueueRefPersistence, BoundedPushFrontOutdatesDroppedTailRef) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  for (auto v : {10u, 20u, 30u})
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  q->AssignFreshIds();

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_front",
                                            {MakeInt(f.arena, 5)}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);  // dropped tail (30) ref outdated
}

// §7.10.3 places push_back in the "never outdates" set with no bounded-queue
// exception (unlike insert/push_front). On a full bounded queue a push_back is
// dropped rather than evicting an existing element, so a reference to the
// highest-numbered element stays valid and its write lands.
TEST(QueueRefPersistence, BoundedPushBackNeverOutdatesExistingRef) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  for (auto v : {10u, 20u, 30u})
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  q->AssignFreshIds();

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                            {MakeInt(f.arena, 40)}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 3u);  // push_back dropped at the bound
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);  // element 30's ref survived
}

// --- Rule B: assigning the entire queue outdates every element reference
// ------

// Updating a queue with an unpacked array concatenation that names the queue
// itself (the §7.10.4 idiom) is an assignment whose target is the whole queue,
// so every outstanding element reference is outdated even though the element
// values are preserved.
TEST(QueueRefPersistence, ConcatAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements = {MakeId(f.arena, "q"), MakeInt(f.arena, 40)};

  RunRefOpThenWrite(f, {MakeAssign(f.arena, "q", concat)},
                    MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);  // no 99: ref outdated by assign
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 40u);
}

}  // namespace
