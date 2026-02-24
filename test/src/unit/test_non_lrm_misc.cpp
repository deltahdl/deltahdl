// Non-LRM tests

#include <gtest/gtest.h>
#include "common/arena.h"
#include "elaboration/const_eval.h"
#include "parser/ast.h"

using namespace delta;

static Expr* LspId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr* LspSelect(Arena& arena, Expr* base, Expr* index) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = index;
  return e;
}

static Expr* LspInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

namespace {

// ============================================================================
// A2: Queue ref binding — basic writeback
// ============================================================================
// Pass q[1] by ref, set v = 99, verify q[1] == 99.
TEST(QueueRef, BasicRefWriteback) {
  QueueRefFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void set_val(ref int v); v = 99; endfunction
  RegAutoFunc(f, "set_val", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MkAssign(f.arena, "v", MkIntLit(f.arena, 99))});

  auto* call = MkCall(f.arena, "set_val", {MkSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

// Ref survives push_front: push_front shifts indices but ref tracks element.
TEST(QueueRef, SurvivesPushFront) {
  QueueRefFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q.push_front(5);   // q[1] (val=20) shifts to q[2]
  //   v = 99;
  // endfunction
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MkExprStmt(f.arena, MkMethodCall(f.arena, "q", "push_front",
                                                {MkIntLit(f.arena, 5)})),
               MkAssign(f.arena, "v", MkIntLit(f.arena, 99))});

  auto* call = MkCall(f.arena, "test_fn", {MkSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {5, 10, 99, 30}. Original q[1] (val=20) shifted to index 2.
  // The ref should have written 99 to index 2 (tracked via element ID).
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

}  // namespace
