// §7.10.3: Persistence of references to elements of a queue

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// ============================================================================
// A3: Outdating — writeback suppressed / preserved
// ============================================================================
// Ref outdated by delete(1): q.delete(1) removes the bound element.
// Write 99 to ref — should NOT propagate back.
TEST(QueueRef, OutdatedByDelete) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q.delete(1);
  //   v = 99;
  // endfunction
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete",
                                                    {MakeInt(f.arena, 1)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {10, 30}. Element 20 was deleted → ref is outdated.
  // 99 should NOT appear in the queue.
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

// Ref outdated by pop_front when the ref points to element 0.
TEST(QueueRef, OutdatedByPopFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q.pop_front();   // removes q[0] (the bound element)
  //   v = 99;
  // endfunction
  RegAutoFunc(
      f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_front", {})),
       MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 0)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {20, 30}. Element 10 was popped → ref is outdated.
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

// Ref survives push_back: push_back never outdates refs.
TEST(QueueRef, SurvivesPushBack) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q.push_back(40);
  //   v = 99;
  // endfunction
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                                    {MakeInt(f.arena, 40)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {10, 99, 30, 40}. q[1] should be 99 (ref survived push_back).
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

}  // namespace
