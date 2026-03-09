#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueueRef, OutdatedByDelete) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete",
                                                    {MakeInt(f.arena, 1)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRef, OutdatedByPopFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(
      f, "test_fn", {{Direction::kRef, false, false, {}, "v", nullptr, {}}},
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_front", {})),
       MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 0)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRef, SurvivesPushBack) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                                    {MakeInt(f.arena, 40)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

}  // namespace
