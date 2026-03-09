#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueueRef, WidthMismatchFallsBackToValue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

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

  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueRef, OutdatedByWholeAssign) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(
      f, "test_fn", {{Direction::kRef, false, false, {}, "v", nullptr, {}}},
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete", {})),
       MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                            {MakeInt(f.arena, 100)})),
       MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                            {MakeInt(f.arena, 200)})),
       MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 100u);
  EXPECT_EQ(q->elements[1].ToUint64(), 200u);
}

TEST(QueueRef, BasicRefWriteback) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "set_val", {{Direction::kRef, false, false, {}, "v", nullptr, {}}},
              {MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "set_val", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

TEST(QueueRef, SurvivesPushFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "test_fn", {{Direction::kRef, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_front",
                                                    {MakeInt(f.arena, 5)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

}  // namespace
