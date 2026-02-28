// §non-lrm:queue_ref

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"
#include "helpers_queue.h"

using namespace delta;

namespace {

// ============================================================================
// A5: §6.22.2 — Type width check
// ============================================================================
// Queue elem_width=32 but function param is 16-bit ref → binding should fail
// and fall back to pass-by-value (write does not propagate).
TEST(QueueRef, WidthMismatchFallsBackToValue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void set_val(ref shortint v); v = 99; endfunction
  // shortint = 16-bit, queue elements are 32-bit.
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "set_val16";
  func->is_automatic = true;
  func->return_type.kind = DataTypeKind::kVoid;
  FunctionArg arg;
  arg.direction = Direction::kRef;
  arg.name = "v";
  arg.data_type.kind = DataTypeKind::kShortint;
  func->func_args = {arg};
  func->func_body_stmts = {MakeAssign(f.arena, "v", MakeInt(f.arena, 99))};
  f.ctx.RegisterFunction("set_val16", func);

  auto* call = MakeCall(f.arena, "set_val16", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // Width mismatch → ref binding rejected → falls back to value.
  // q[1] should still be 20.
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

// Ref outdated by whole-queue assignment.
TEST(QueueRef, OutdatedByWholeAssign) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q = '{100, 200};   // whole-queue assignment
  //   v = 99;
  // endfunction
  //
  // We simulate the whole-queue assignment as: q.delete(); then push 100, 200.
  // (A real whole-queue assign goes through stmt_assign.cpp, which is harder to
  //  invoke from a function body in a unit test. This achieves the same effect:
  //  all element IDs are replaced → ref is outdated.)
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete", {})),
               MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                                {MakeInt(f.arena, 100)})),
               MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                                {MakeInt(f.arena, 200)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  // q now has {100, 200}. All original IDs are gone → ref is outdated.
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 100u);
  EXPECT_EQ(q->elements[1].ToUint64(), 200u);
}

// ============================================================================
// A2: Queue ref binding — basic writeback
// ============================================================================
// Pass q[1] by ref, set v = 99, verify q[1] == 99.
TEST(QueueRef, BasicRefWriteback) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void set_val(ref int v); v = 99; endfunction
  RegAutoFunc(f, "set_val", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "set_val", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

// Ref survives push_front: push_front shifts indices but ref tracks element.
TEST(QueueRef, SurvivesPushFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  // function automatic void test_fn(ref int v);
  //   q.push_front(5);   // q[1] (val=20) shifts to q[2]
  //   v = 99;
  // endfunction
  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_front",
                                                {MakeInt(f.arena, 5)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
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
