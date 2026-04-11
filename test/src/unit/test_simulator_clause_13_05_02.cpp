#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(PassByRef, WriteThroughRefModifiesCaller) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 50);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add_ten";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kRef, false, false, false, {}, "r", nullptr, {}}};
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "r"),
                         MakeInt(f.arena, 10));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "r", rhs));
  f.ctx.RegisterFunction("add_ten", func);

  auto* call = MakeCall(f.arena, "add_ten", {MakeId(f.arena, "x")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 60u);
}

TEST(PassByRef, PassByRefReadsCaller) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 25);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_ref";
  func->func_args = {{Direction::kRef, false, false, false, {}, "r", nullptr, {}}};
  auto* body_expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "r"),
                               MakeInt(f.arena, 3));
  func->func_body_stmts.push_back(MakeReturn(f.arena, body_expr));
  f.ctx.RegisterFunction("read_ref", func);

  auto* call = MakeCall(f.arena, "read_ref", {MakeId(f.arena, "x")});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 75u);
}

TEST(QueueRef, RefReadsCurrentValue) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "read_ref";
  func->is_automatic = true;
  func->func_args = {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}};
  func->func_body_stmts = {MakeReturn(f.arena, MakeId(f.arena, "v"))};
  f.ctx.RegisterFunction("read_ref", func);

  auto* call = MakeCall(f.arena, "read_ref", {MakeSelect(f.arena, "q", 1)});
  EXPECT_EQ(EvalExpr(call, f.ctx, f.arena).ToUint64(), 20u);
}

TEST(PassByRef, RefImmediateVisibility) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "write_and_read";
  func->func_args = {{Direction::kRef, false, false, false, {}, "r", nullptr, {}}};

  func->func_body_stmts.push_back(
      MakeAssign(f.arena, "r", MakeInt(f.arena, 42)));
  func->func_body_stmts.push_back(MakeReturn(f.arena, MakeId(f.arena, "r")));
  f.ctx.RegisterFunction("write_and_read", func);

  auto* call = MakeCall(f.arena, "write_and_read", {MakeId(f.arena, "x")});
  auto result = EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 42u);
  EXPECT_EQ(result.ToUint64(), 42u);
}

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

TEST(QueueRef, BasicRefWriteback) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "set_val",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "set_val", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

TEST(QueueRef, OutdatedByDelete) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
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
      f, "test_fn", {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_front", {})),
       MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 0)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRef, OutdatedByPopBack) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(
      f, "test_fn", {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_back", {})),
       MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 2)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueRef, SurvivesPushBack) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                                    {MakeInt(f.arena, 40)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

TEST(QueueRef, SurvivesPushFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
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

TEST(QueueRef, SurvivesInsert) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "insert",
                                                    {MakeInt(f.arena, 0),
                                                     MakeInt(f.arena, 5)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

TEST(QueueRef, OutdatedByWholeAssign) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(
      f, "test_fn", {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
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

TEST(QueueRef, OutdatedByConcatAssign) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements = {MakeId(f.arena, "q"), MakeInt(f.arena, 40)};
  auto* assign_q = MakeAssign(f.arena, "q", concat);

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {assign_q, MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 1)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 40u);
}

TEST(QueueRef, DeletePreservesOtherRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete",
                                                    {MakeInt(f.arena, 1)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 0)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 99u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRef, PopFrontPreservesOtherRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(
      f, "test_fn", {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_front", {})),
       MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 2)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

TEST(QueueRef, PopBackPreservesOtherRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(
      f, "test_fn", {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_back", {})),
       MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 0)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 99u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueRef, BoundedPushFrontOutdatesLastElement) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  for (auto v : {10u, 20u, 30u})
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  q->AssignFreshIds();

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_front",
                                                    {MakeInt(f.arena, 5)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 2)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
}

TEST(QueueRef, BoundedInsertOutdatesLastElement) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  for (auto v : {10u, 20u, 30u})
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  q->AssignFreshIds();

  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "insert",
                                                    {MakeInt(f.arena, 0),
                                                     MakeInt(f.arena, 5)})),
               MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "test_fn", {MakeSelect(f.arena, "q", 2)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
}

TEST(PassByRef, SwapViaRef) {
  FuncFixture f;

  auto* a_var = f.ctx.CreateVariable("a", 32);
  a_var->value = MakeLogic4VecVal(f.arena, 32, 10);
  auto* b_var = f.ctx.CreateVariable("b", 32);
  b_var->value = MakeLogic4VecVal(f.arena, 32, 20);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "swap";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "x", nullptr, {}},
      {Direction::kRef, false, false, false, {}, "y", nullptr, {}},
  };
  func->func_body_stmts = {
      MakeAssign(f.arena, "tmp", MakeId(f.arena, "x")),
      MakeAssign(f.arena, "x", MakeId(f.arena, "y")),
      MakeAssign(f.arena, "y", MakeId(f.arena, "tmp")),
  };
  f.ctx.RegisterFunction("swap", func);

  auto* call =
      MakeCall(f.arena, "swap", {MakeId(f.arena, "a"), MakeId(f.arena, "b")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(a_var->value.ToUint64(), 20u);
  EXPECT_EQ(b_var->value.ToUint64(), 10u);
}

TEST(PassByRef, NonIdentifierArgFallsBackToValueCopy) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 5);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add_ten";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kRef, false, false, false, {}, "r", nullptr, {}}};
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "r"),
                         MakeInt(f.arena, 10));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "r", rhs));
  f.ctx.RegisterFunction("add_ten", func);

  auto* arg_expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "x"),
                              MakeInt(f.arena, 1));
  auto* call = MakeCall(f.arena, "add_ten", {arg_expr});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 5u);
}

TEST(PassByRef, TwoRefsToSameVariable) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 100);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "double_ref";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "a", nullptr, {}},
      {Direction::kRef, false, false, false, {}, "b", nullptr, {}},
  };
  func->func_body_stmts = {
      MakeAssign(f.arena, "a", MakeInt(f.arena, 42)),
  };
  f.ctx.RegisterFunction("double_ref", func);

  auto* call = MakeCall(f.arena, "double_ref",
                        {MakeId(f.arena, "x"), MakeId(f.arena, "x")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 42u);
}

TEST(PassByRef, BothRefsToSameVariableSeeWrites) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "inc_both";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "a", nullptr, {}},
      {Direction::kRef, false, false, false, {}, "b", nullptr, {}},
  };
  func->func_body_stmts = {
      MakeAssign(f.arena, "a", MakeInt(f.arena, 10)),
      MakeAssign(f.arena, "b",
                 MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "b"),
                            MakeInt(f.arena, 5))),
  };
  f.ctx.RegisterFunction("inc_both", func);

  auto* call = MakeCall(f.arena, "inc_both",
                        {MakeId(f.arena, "x"), MakeId(f.arena, "x")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 15u);
}

TEST(PassByRef, CallSyntaxTransparentForRef) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 7);

  auto* by_ref = f.arena.Create<ModuleItem>();
  by_ref->kind = ModuleItemKind::kFunctionDecl;
  by_ref->name = "triple_ref";
  by_ref->func_args = {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}};
  by_ref->func_body_stmts = {MakeReturn(
      f.arena, MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "v"),
                          MakeInt(f.arena, 3)))};
  f.ctx.RegisterFunction("triple_ref", by_ref);

  auto* by_val = f.arena.Create<ModuleItem>();
  by_val->kind = ModuleItemKind::kFunctionDecl;
  by_val->name = "triple_val";
  by_val->func_args = {
      {Direction::kInput, false, false, false, {}, "v", nullptr, {}}};
  by_val->func_body_stmts = {MakeReturn(
      f.arena, MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "v"),
                          MakeInt(f.arena, 3)))};
  f.ctx.RegisterFunction("triple_val", by_val);

  auto* call_ref =
      MakeCall(f.arena, "triple_ref", {MakeId(f.arena, "x")});
  auto* call_val =
      MakeCall(f.arena, "triple_val", {MakeId(f.arena, "x")});

  EXPECT_EQ(EvalExpr(call_ref, f.ctx, f.arena).ToUint64(), 21u);
  EXPECT_EQ(EvalExpr(call_val, f.ctx, f.arena).ToUint64(), 21u);
}

TEST(QueueRef, QueueRefOutOfBoundsFallsBackToValue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(f, "set_val",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              {MakeAssign(f.arena, "v", MakeInt(f.arena, 99))});

  auto* call = MakeCall(f.arena, "set_val", {MakeSelect(f.arena, "q", 5)});
  EvalExpr(call, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(PassByRef, RefArgDoesNotCopyBack) {
  FuncFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 100);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "set_ref";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kRef, false, false, false, {}, "r", nullptr, {}}};
  func->func_body_stmts = {
      MakeAssign(f.arena, "r", MakeInt(f.arena, 77)),
  };
  f.ctx.RegisterFunction("set_ref", func);

  auto* call = MakeCall(f.arena, "set_ref", {MakeId(f.arena, "x")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 77u);
}

}  // namespace
