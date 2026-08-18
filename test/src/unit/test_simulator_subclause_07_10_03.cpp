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

#include <algorithm>
#include <cstdint>
#include <vector>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

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

// `q.<name>`, the parenthesis-less spelling of an array manipulation method
// call that §7.12's Syntax 7-5 allows by making the argument list optional.
// This is the spelling the simulator serves the ordering methods of a queue
// through; #3236 tracks the parenthesized one, which reaches nothing.
Expr* MakeMemberAccess(Arena& arena, std::string_view obj,
                       std::string_view field) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kMemberAccess;
  e->lhs = MakeId(arena, obj);
  e->rhs = MakeId(arena, field);
  return e;
}

// `q[lo:hi]`, the right-hand side of the §7.10.4 assignment forms that shorten
// a queue.
Expr* MakeSlice(Arena& arena, std::string_view name, Expr* lo, Expr* hi) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = MakeId(arena, name);
  e->index = lo;
  e->index_end = hi;
  return e;
}

// `{}`, which §7.10 makes the empty queue.
Expr* MakeEmptyConcat(Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kConcatenation;
  return e;
}

// `new[size]`, the §7.5.1 form that resizes a queue.
Expr* MakeNewSized(Arena& arena, uint64_t size) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->text = "new";
  e->args.push_back(MakeInt(arena, size));
  return e;
}

// What the queue `q` holds after `src` has run, together with the identities
// its elements carried before the initial block ran. §7.10.3 says which
// identities an operation may discard, so a test of it has to see them from
// both sides of the operation, and the declaration initializer has run by the
// time lowering finishes while the initial block has not.
struct QueueAcrossRun {
  QueueObject* q;
  std::vector<uint64_t> ids_before;
};

QueueAcrossRun RunAndCaptureIds(const char* src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  if (!design) return {nullptr, {}};
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* q = f.ctx.FindQueue("q");
  std::vector<uint64_t> before;
  if (q) before = q->element_ids;
  f.scheduler.Run();
  return {q, before};
}

// Whether any element of `q` still carries one of the identities in `before`.
// A reference is outdated exactly when the identity it was taken on is gone,
// so this answers whether every reference to the queue's earlier elements has
// been outdated.
bool AnyIdSurvives(const QueueAcrossRun& r) {
  return std::any_of(
      r.ids_before.begin(), r.ids_before.end(), [&](uint64_t id) {
        return std::find(r.q->element_ids.begin(), r.q->element_ids.end(),
                         id) != r.q->element_ids.end();
      });
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

// --- Rule A: an ordering method removes nothing, so every reference survives
// ------------------

// §7.10.3: sort removes no element, so a reference stays valid and follows the
// element it was taken on to wherever that element sorted. The reference here
// is taken on the element holding 30, which sorts from the front to the back,
// so the write of 99 has to land at the back rather than at the index the
// reference was taken at.
TEST(QueueRefPersistence, SortLeavesRefFollowingItsElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {30, 10, 20});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMemberAccess(f.arena, "q", "sort"))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
}

// §7.10.3: rsort removes no element either, and the element holding 10 moves
// from the front to the back.
TEST(QueueRefPersistence, RsortLeavesRefFollowingItsElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 30, 20});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMemberAccess(f.arena, "q", "rsort"))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 30u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
}

// §7.10.3: reverse removes no element, and moves the element holding 10 from
// the front to the back.
TEST(QueueRefPersistence, ReverseLeavesRefFollowingItsElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMemberAccess(f.arena, "q", "reverse"))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 30u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
}

// §7.10.3: shuffle removes no element, so the reference taken on the element
// holding 20 stays valid and the write of 99 replaces that element wherever it
// landed. The permutation is not predictable, so the claim is stated as what
// holds for every permutation: the value written is somewhere and the value it
// replaced is nowhere. A reference outdated by the shuffle would leave 20 in
// the queue and 99 out of it.
TEST(QueueRefPersistence, ShuffleLeavesRefValid) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMemberAccess(f.arena, "q", "shuffle"))},
      MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 3u);
  size_t wrote = 0, kept = 0;
  for (const auto& e : q->elements) {
    if (e.ToUint64() == 99u) ++wrote;
    if (e.ToUint64() == 20u) ++kept;
  }
  EXPECT_EQ(wrote, 1u);
  EXPECT_EQ(kept, 0u);
}

// --- Rule B: the other whole-queue assignment forms
// ------------------

// §7.10.3 with §7.10.4: `q = q[1:$]` is an assignment whose target is the
// entire queue, so it outdates a reference to every element of the original
// queue -- including the element holding 20, which the slice keeps. A method
// that dropped only the elements it removed would leave that reference valid,
// which is the difference §7.10.4 draws between the assignment form and
// `q.pop_front()`.
TEST(QueueRefPersistence, SliceAssignOutdatesEvenSurvivingElementRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(f,
                    {MakeAssign(f.arena, "q",
                                MakeSlice(f.arena, "q", MakeInt(f.arena, 1),
                                          MakeId(f.arena, "$")))},
                    MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

// §7.10.3: `q = {}` assigns the whole queue the empty queue, so every
// reference is outdated and the write through the held one is dropped.
TEST(QueueRefPersistence, EmptyConcatAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(f, {MakeAssign(f.arena, "q", MakeEmptyConcat(f.arena))},
                    MakeSelect(f.arena, "q", 1));

  EXPECT_EQ(q->elements.size(), 0u);
}

// §7.10.3: `q = new[2]` is an assignment whose target is the entire queue, so
// the reference held to the element that keeps both its value and its index is
// outdated with the rest.
TEST(QueueRefPersistence, NewSizedAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(f, {MakeAssign(f.arena, "q", MakeNewSized(f.arena, 2))},
                    MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// --- Rule B over the §11.4.14.4 streaming unpack
// ------------------

// §7.10.3: a streaming unpack that sizes a queue from the stream replaces
// every element the queue held, so no element may carry an identity from
// before it ran. Leaving those identities in place lets a reference taken
// before the unpack write over an element the unpack produced.
TEST(QueueRefPersistence, GreedyStreamUnpackOutdatesAllRefs) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte q[$] = {8'h11, 8'h22, 8'h33};\n"
      "  logic [7:0] trailer;\n"
      "  initial begin\n"
      "    {>> byte {q, trailer}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  ASSERT_EQ(r.ids_before.size(), 3u);
  EXPECT_FALSE(AnyIdSurvives(r));
}

// §7.10.3: the same unpack leaves one identity per element, so a reference
// taken after it can be recorded and written back. An element with no identity
// is unreachable by any later reference.
TEST(QueueRefPersistence, GreedyStreamUnpackGivesEveryElementAnIdentity) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte q[$] = {8'h11, 8'h22, 8'h33};\n"
      "  logic [7:0] trailer;\n"
      "  initial begin\n"
      "    {>> byte {q, trailer}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  EXPECT_EQ(r.q->element_ids.size(), r.q->elements.size());
}

// §7.10.3: a second queue on the left of one streaming unpack takes no bits
// and is emptied, so every element it held is removed and every reference to
// one is outdated. An identity left behind on an empty queue is claimed again
// by the next element pushed onto it.
TEST(QueueRefPersistence, SecondStreamQueueEmptiedOutdatesAllRefs) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte p[$];\n"
      "  byte q[$] = {8'h11, 8'h22, 8'h33};\n"
      "  initial begin\n"
      "    {>> byte {p, q}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  ASSERT_EQ(r.ids_before.size(), 3u);
  EXPECT_TRUE(r.q->element_ids.empty());
}

// §7.10.3: a with-range unpack names the slots it writes and grows the queue
// to reach them. Growing removes nothing, so the elements already there keep
// the identities any reference to them was taken on.
TEST(QueueRefPersistence, WithRangeStreamUnpackKeepsExistingIdentities) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte q[$] = {8'h11, 8'h22};\n"
      "  initial begin\n"
      "    {<< byte {q with [0 +: 4]}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  ASSERT_EQ(r.ids_before.size(), 2u);
  ASSERT_GE(r.q->element_ids.size(), 2u);
  EXPECT_EQ(r.q->element_ids[0], r.ids_before[0]);
  EXPECT_EQ(r.q->element_ids[1], r.ids_before[1]);
}

// §7.10.3: the elements that unpack grows onto the end are new, and each needs
// an identity of its own. Without one the identity list is shorter than the
// element list, and a later pop_back then discards the identity of an element
// it did not remove -- outdating a reference the clause says survives.
TEST(QueueRefPersistence, WithRangeStreamUnpackGivesGrownElementsIdentities) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte q[$] = {8'h11, 8'h22};\n"
      "  initial begin\n"
      "    {<< byte {q with [0 +: 4]}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  EXPECT_EQ(r.q->element_ids.size(), r.q->elements.size());
}

}  // namespace
