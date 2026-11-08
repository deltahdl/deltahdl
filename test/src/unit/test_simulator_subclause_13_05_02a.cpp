#include <gtest/gtest.h>

#include <cstdint>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "helpers_queue_ref_method.h"
#include "helpers_scheduler.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

Variable* SetupAddTenFunc(FuncFixture& f, uint64_t x_init) {
  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, x_init);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "add_ten";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "r", nullptr, {}}};
  auto* rhs = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "r"),
                         MakeInt(f.arena, 10));
  func->func_body_stmts.push_back(MakeAssign(f.arena, "r", rhs));
  f.ctx.RegisterFunction("add_ten", func);
  return x_var;
}

TEST(PassByRef, WriteThroughRefModifiesCaller) {
  FuncFixture f;
  auto* x_var = SetupAddTenFunc(f, 50);

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
  func->return_type.kind = DataTypeKind::kInt;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "r", nullptr, {}}};
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
  func->return_type.kind = DataTypeKind::kInt;
  func->is_automatic = true;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "v", nullptr, {}}};
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
  func->return_type.kind = DataTypeKind::kInt;
  func->func_args = {
      {Direction::kRef, false, false, false, {}, "r", nullptr, {}}};

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

  RunQueueRefMethodThenAssign(f, "q", "delete", {MakeInt(f.arena, 1)}, 1);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRef, OutdatedByPopFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunQueueRefMethodThenAssign(f, "q", "pop_front", {}, 0);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRef, OutdatedByPopBack) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunQueueRefMethodThenAssign(f, "q", "pop_back", {}, 2);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueRef, SurvivesPushBack) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunQueueRefMethodThenAssign(f, "q", "push_back", {MakeInt(f.arena, 40)}, 1);

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

TEST(QueueRef, SurvivesPushFront) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunQueueRefMethodThenAssign(f, "q", "push_front", {MakeInt(f.arena, 5)}, 1);

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

TEST(QueueRef, SurvivesInsert) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunQueueRefMethodThenAssign(f, "q", "insert",
                              {MakeInt(f.arena, 0), MakeInt(f.arena, 5)}, 1);

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

TEST(QueueRef, OutdatedByDeleteAllNotReclaimedByLaterPush) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RegAutoFunc(
      f, "test_fn",
      {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
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

  RunQueueRefMethodThenAssign(f, "q", "delete", {MakeInt(f.arena, 1)}, 0);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 99u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRef, PopFrontPreservesOtherRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunQueueRefMethodThenAssign(f, "q", "pop_front", {}, 2);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

TEST(QueueRef, PopBackPreservesOtherRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunQueueRefMethodThenAssign(f, "q", "pop_back", {}, 0);

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 99u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueRef, BoundedPushFrontOutdatesLastElement) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, "q", 3, {10, 20, 30});

  RunQueueRefMethodThenAssign(f, "q", "push_front", {MakeInt(f.arena, 5)}, 2);

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
}

TEST(QueueRef, BoundedInsertOutdatesLastElement) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, "q", 3, {10, 20, 30});

  RunQueueRefMethodThenAssign(f, "q", "insert",
                              {MakeInt(f.arena, 0), MakeInt(f.arena, 5)}, 2);

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
  auto* tmp_decl = f.arena.Create<Stmt>();
  tmp_decl->kind = StmtKind::kVarDecl;
  tmp_decl->var_name = "tmp";
  tmp_decl->var_decl_type.kind = DataTypeKind::kInt;
  func->func_body_stmts = {
      tmp_decl,
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
  auto* x_var = SetupAddTenFunc(f, 5);

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
  by_ref->return_type.kind = DataTypeKind::kInt;
  by_ref->func_args = {
      {Direction::kRef, false, false, false, {}, "v", nullptr, {}}};
  by_ref->func_body_stmts = {MakeReturn(
      f.arena, MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "v"),
                          MakeInt(f.arena, 3)))};
  f.ctx.RegisterFunction("triple_ref", by_ref);

  auto* by_val = f.arena.Create<ModuleItem>();
  by_val->kind = ModuleItemKind::kFunctionDecl;
  by_val->name = "triple_val";
  by_val->return_type.kind = DataTypeKind::kInt;
  by_val->func_args = {
      {Direction::kInput, false, false, false, {}, "v", nullptr, {}}};
  by_val->func_body_stmts = {MakeReturn(
      f.arena, MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "v"),
                          MakeInt(f.arena, 3)))};
  f.ctx.RegisterFunction("triple_val", by_val);

  auto* call_ref = MakeCall(f.arena, "triple_ref", {MakeId(f.arena, "x")});
  auto* call_val = MakeCall(f.arena, "triple_val", {MakeId(f.arena, "x")});

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

TEST(QueueRef, RefElementWritebackWakesAnAlwaysCombReadingTheElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int b;\n"
      "  function automatic void poke(ref int r);\n"
      "    r = 99;\n"
      "  endfunction\n"
      "  always_comb b = q[1];\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    #1 poke(q[1]);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 99u);
}

TEST(QueueRef, RefElementWritebackWakesAnEventControlOnThatElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int woke;\n"
      "  function automatic void poke(ref int r);\n"
      "    r = 99;\n"
      "  endfunction\n"
      "  always @(q[1]) woke = woke + 1;\n"
      "  initial begin\n"
      "    woke = 0;\n"
      "    #1 q.push_back(10);\n"
      "    #1 q.push_back(20);\n"
      "    #1 poke(q[1]);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "woke");
  EXPECT_EQ(v, 2u);
}

TEST(PassByRef, AssocRefElementWritebackWakesAnAlwaysCombReadingTheElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int b;\n"
      "  function automatic void poke(ref int r);\n"
      "    r = 99;\n"
      "  endfunction\n"
      "  always_comb b = aa[1];\n"
      "  initial begin\n"
      "    #1 poke(aa[1]);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 99u);
}

TEST(PassByRef, RefWholeVariableWriteWakesAnAlwaysCombReadingIt) {
  auto v = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  int b;\n"
      "  function automatic void poke(ref int r);\n"
      "    r = 99;\n"
      "  endfunction\n"
      "  always_comb b = x;\n"
      "  initial begin\n"
      "    #1 poke(x);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 99u);
}

TEST(QueueRef, TypedefRefFormalBindsToTheQueueElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  nib q[$];\n"
      "  int r;\n"
      "  task automatic bump(ref nib e);\n"
      "    e = e + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    q.push_back(4'd5);\n"
      "    bump(q[0]);\n"
      "    r = q[0];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 6u);
}

TEST(PassByRef, TypedefRefFormalBindsToTheAssocElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  nib aa[int];\n"
      "  int r;\n"
      "  task automatic bump(ref nib e);\n"
      "    e = e + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    aa[3] = 4'd5;\n"
      "    bump(aa[3]);\n"
      "    r = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 6u);
}

TEST(QueueRef, RefFormalOfANonEquivalentTypedefDoesNotBind) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  typedef bit [7:0] octet;\n"
      "  nib q[$];\n"
      "  int r;\n"
      "  task automatic bump(ref octet e);\n"
      "    e = e + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    q.push_back(4'd5);\n"
      "    bump(q[0]);\n"
      "    r = q[0];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 5u);
}

TEST(ArgumentPassingSim, OutputActualSpelledLikeTheFormalIsWritten) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  task count_up(output int met);\n"
      "    met = 0;\n"
      "    met += 3;\n"
      "  endtask\n"
      "  function void twice(inout int n);\n"
      "    n = n * 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int met, n;\n"
      "    n = 5;\n"
      "    count_up(met);\n"
      "    twice(n);\n"
      "    r = met * 100 + n;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 310u);
}

TEST(PassByRef, ClassTypedRefFormalOfAMethodReplacesTheCallersObject) {
  auto val = RunAndGet(
      "class C; int v; endclass\n"
      "class Maker;\n"
      "  function void remake(ref C r, input int x);\n"
      "    r = new; r.v = x;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  Maker m = new;\n"
      "  C b;\n"
      "  int res;\n"
      "  initial begin\n"
      "    m.remake(b, 62);\n"
      "    res = (b == null) ? 1 : b.v;\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 62u);
}

TEST(PassByRef, ClassTypedRefFormalBesideAnIntRefFormalBothAliasTheCaller) {
  auto val = RunAndGet(
      "class C; int v;\n"
      "  function void set(int x); v = x; endfunction\n"
      "endclass\n"
      "class U;\n"
      "  function void touch(ref C h, ref int cnt);\n"
      "    if (h == null) h = new;\n"
      "    h.set(40); cnt++;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  U u = new; C c; int n = 2;\n"
      "  int res;\n"
      "  initial begin\n"
      "    u.touch(c, n);\n"
      "    res = ((c == null) ? 1 : c.v) * 100 + n;\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 4003u);
}

TEST(PassByRef, ClassTypedRefFormalOfAModuleTaskRebindsTheCallersHandle) {
  auto val = RunAndGet(
      "class C; int v; endclass\n"
      "module t;\n"
      "  C a, b;\n"
      "  int res;\n"
      "  task automatic rebind(ref C h, input C other);\n"
      "    h = other; h.v = 5;\n"
      "    h = new; h.v = 7;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = new; a.v = 1;\n"
      "    rebind(b, a);\n"
      "    res = ((b == null) ? 1 : b.v) * 10 + a.v;\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 75u);
}

TEST(PassByRef, RefFormalOfAFixedArrayScalesTheCallersElements) {
  auto val = RunAndGet(
      "module t;\n"
      "  int arr[3] = '{1, 2, 3};\n"
      "  int res;\n"
      "  task automatic scale(ref int a[3]);\n"
      "    foreach (a[i]) a[i] = a[i] * 5;\n"
      "  endtask\n"
      "  initial begin\n"
      "    scale(arr);\n"
      "    res = arr[0] * 10000 + arr[1] * 100 + arr[2];\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 51015u);
}

TEST(PassByRef, RefFormalOfAQueueGrowsTheCallersQueue) {
  auto val = RunAndGet(
      "module t;\n"
      "  int q[$] = '{42};\n"
      "  int res;\n"
      "  task automatic push(ref int qq[$]);\n"
      "    qq.push_front(3); qq.push_back(7);\n"
      "  endtask\n"
      "  initial begin\n"
      "    push(q);\n"
      "    res = q.size() * 100000 + q[0] * 10000 + q[1] * 100 + q[2];\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 334207u);
}

TEST(PassByRef, RefFormalOfAnAssocArrayFillsTheCallersArray) {
  auto val = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int res;\n"
      "  task automatic fill(ref int m[string]);\n"
      "    m[\"x\"] = 100; m[\"y\"] = 200;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fill(aa);\n"
      "    res = aa.size() * 1000 + aa[\"x\"];\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 2100u);
}

TEST(PassByRef, RefFormalOfAnUnpackedStructWritesTheCallersMembers) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef struct { int a; int b; } st_t;\n"
      "  st_t s;\n"
      "  int res;\n"
      "  task automatic fs(ref st_t x); x.a = 8; x.b = 9; endtask\n"
      "  initial begin\n"
      "    fs(s);\n"
      "    res = s.a * 10 + s.b;\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 89u);
}

TEST(PassByRef, ConstRefFormalOfAFixedArrayReadsTheCallersElements) {
  auto val = RunAndGet(
      "module t;\n"
      "  byte data[4] = '{10, 20, 5, 25};\n"
      "  int res;\n"
      "  function automatic int one(const ref byte d[4]);\n"
      "    return d[1];\n"
      "  endfunction\n"
      "  function automatic int total(const ref byte d[4]);\n"
      "    int s = 0;\n"
      "    foreach (d[i]) s += d[i];\n"
      "    return s;\n"
      "  endfunction\n"
      "  initial res = one(data) * 100 + total(data);\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 2060u);
}

TEST(PassByRef, RefFormalBoundToAFixedArrayElementWritesTheElement) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 7;\n"
      "  int arr[3];\n"
      "  int res;\n"
      "  task automatic add(ref int r, input int n); r = r + n; endtask\n"
      "  initial begin\n"
      "    add(x, 5);\n"
      "    arr[2] = 40; add(arr[2], 5);\n"
      "    res = x * 100 + arr[2];\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 1245u);
}

TEST(PassByRef, RefFormalBoundToAStructMemberOrAClassPropertyWritesIt) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef struct { int a; int b; } st_t;\n"
      "  class C; int v = 60; endclass\n"
      "  st_t s;\n"
      "  C h = new;\n"
      "  int res;\n"
      "  task automatic add(ref int r, input int n); r = r + n; endtask\n"
      "  initial begin\n"
      "    s.a = 1; s.b = 5;\n"
      "    add(s.b, 20);\n"
      "    add(h.v, 5);\n"
      "    res = s.a * 10000 + s.b * 100 + h.v;\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 12565u);
}

}  // namespace
