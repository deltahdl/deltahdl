// §13.5: Subroutine calls and argument passing

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>

using namespace delta;

struct ExprFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

namespace {

// =============================================================================
// Function output argument writeback
// =============================================================================
TEST(Eval, FunctionOutputArgWriteback) {
  ExprFixture f;

  // Create variable "result" in global scope.
  auto *result_var = f.ctx.CreateVariable("result", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Build function: function void compute(input int a, output int b);
  //   b = a * 2;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "compute";
  func->func_args = {
      {Direction::kInput, false, {}, "a", nullptr, {}},
      {Direction::kOutput, false, {}, "b", nullptr, {}},
  };

  // Body: b = a * 2
  auto *lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "b";

  auto *a_ref = f.arena.Create<Expr>();
  a_ref->kind = ExprKind::kIdentifier;
  a_ref->text = "a";

  auto *two = f.arena.Create<Expr>();
  two->kind = ExprKind::kIntegerLiteral;
  two->int_val = 2;

  auto *mul = f.arena.Create<Expr>();
  mul->kind = ExprKind::kBinary;
  mul->op = TokenKind::kStar;
  mul->lhs = a_ref;
  mul->rhs = two;

  auto *assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = mul;
  func->func_body_stmts.push_back(assign);

  f.ctx.RegisterFunction("compute", func);

  // Build call expression: compute(21, result)
  auto *arg0 = f.arena.Create<Expr>();
  arg0->kind = ExprKind::kIntegerLiteral;
  arg0->int_val = 21;

  auto *arg1 = f.arena.Create<Expr>();
  arg1->kind = ExprKind::kIdentifier;
  arg1->text = "result";

  auto *call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "compute";
  call->args = {arg0, arg1};

  EvalExpr(call, f.ctx, f.arena);

  // Output arg "b" should have been written back to "result".
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(Eval, FunctionInoutArgWriteback) {
  ExprFixture f;

  // Create variable "x" with initial value 10.
  auto *x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 10);

  // Build function: function void increment(inout int v);
  //   v = v + 1;
  // endfunction
  auto *func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "increment";
  func->func_args = {{Direction::kInout, false, {}, "v", nullptr, {}}};

  auto *lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "v";

  auto *v_ref = f.arena.Create<Expr>();
  v_ref->kind = ExprKind::kIdentifier;
  v_ref->text = "v";

  auto *one = f.arena.Create<Expr>();
  one->kind = ExprKind::kIntegerLiteral;
  one->int_val = 1;

  auto *add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = v_ref;
  add->rhs = one;

  auto *assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = add;
  func->func_body_stmts.push_back(assign);

  f.ctx.RegisterFunction("increment", func);

  // Build call: increment(x)
  auto *arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "x";

  auto *call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "increment";
  call->args = {arg};

  EvalExpr(call, f.ctx, f.arena);

  // Inout arg "v" should read 10 and write back 11 to "x".
  EXPECT_EQ(x_var->value.ToUint64(), 11u);
}

TEST(Eval, NestedFunctionOutputArgs) {
  ExprFixture f;

  auto *result_var = f.ctx.CreateVariable("result", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // inner(input int a, output int b): b = a + 100
  auto *inner = f.arena.Create<ModuleItem>();
  inner->kind = ModuleItemKind::kFunctionDecl;
  inner->name = "inner";
  inner->func_args = {
      {Direction::kInput, false, {}, "a", nullptr, {}},
      {Direction::kOutput, false, {}, "b", nullptr, {}},
  };
  auto *inner_lhs = f.arena.Create<Expr>();
  inner_lhs->kind = ExprKind::kIdentifier;
  inner_lhs->text = "b";
  auto *inner_a = f.arena.Create<Expr>();
  inner_a->kind = ExprKind::kIdentifier;
  inner_a->text = "a";
  auto *hundred = f.arena.Create<Expr>();
  hundred->kind = ExprKind::kIntegerLiteral;
  hundred->int_val = 100;
  auto *inner_add = f.arena.Create<Expr>();
  inner_add->kind = ExprKind::kBinary;
  inner_add->op = TokenKind::kPlus;
  inner_add->lhs = inner_a;
  inner_add->rhs = hundred;
  auto *inner_assign = f.arena.Create<Stmt>();
  inner_assign->kind = StmtKind::kBlockingAssign;
  inner_assign->lhs = inner_lhs;
  inner_assign->rhs = inner_add;
  inner->func_body_stmts.push_back(inner_assign);
  f.ctx.RegisterFunction("inner", inner);

  // outer(input int x, output int y): inner(x, y)
  auto *outer = f.arena.Create<ModuleItem>();
  outer->kind = ModuleItemKind::kFunctionDecl;
  outer->name = "outer";
  outer->func_args = {
      {Direction::kInput, false, {}, "x", nullptr, {}},
      {Direction::kOutput, false, {}, "y", nullptr, {}},
  };
  auto *call_arg0 = f.arena.Create<Expr>();
  call_arg0->kind = ExprKind::kIdentifier;
  call_arg0->text = "x";
  auto *call_arg1 = f.arena.Create<Expr>();
  call_arg1->kind = ExprKind::kIdentifier;
  call_arg1->text = "y";
  auto *inner_call = f.arena.Create<Expr>();
  inner_call->kind = ExprKind::kCall;
  inner_call->callee = "inner";
  inner_call->args = {call_arg0, call_arg1};
  auto *call_stmt = f.arena.Create<Stmt>();
  call_stmt->kind = StmtKind::kExprStmt;
  call_stmt->expr = inner_call;
  outer->func_body_stmts.push_back(call_stmt);
  f.ctx.RegisterFunction("outer", outer);

  // Call outer(5, result)
  auto *arg0 = f.arena.Create<Expr>();
  arg0->kind = ExprKind::kIntegerLiteral;
  arg0->int_val = 5;
  auto *arg1 = f.arena.Create<Expr>();
  arg1->kind = ExprKind::kIdentifier;
  arg1->text = "result";
  auto *call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "outer";
  call->args = {arg0, arg1};

  EvalExpr(call, f.ctx, f.arena);

  // inner sets b = 5 + 100 = 105, which writes back to outer's "y",
  // which then writes back to caller's "result".
  EXPECT_EQ(result_var->value.ToUint64(), 105u);
}

} // namespace
