#include "fixture_simulator.h"
#include "simulator/eval.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimA609, TaskCallWithArgs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task set_val(input logic [7:0] v);\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_val(8'd99);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(SimA82, TfCallTaskOutputArg) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task get_val(output logic [7:0] v);\n"
      "    v = 8'd33;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    get_val(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(Eval, NestedFunctionOutputArgs) {
  ExprFixture f;

  auto* result_var = f.ctx.CreateVariable("result", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* inner = f.arena.Create<ModuleItem>();
  inner->kind = ModuleItemKind::kFunctionDecl;
  inner->name = "inner";
  inner->func_args = {
      {Direction::kInput, false, {}, "a", nullptr, {}},
      {Direction::kOutput, false, {}, "b", nullptr, {}},
  };
  auto* inner_lhs = f.arena.Create<Expr>();
  inner_lhs->kind = ExprKind::kIdentifier;
  inner_lhs->text = "b";
  auto* inner_a = f.arena.Create<Expr>();
  inner_a->kind = ExprKind::kIdentifier;
  inner_a->text = "a";
  auto* hundred = f.arena.Create<Expr>();
  hundred->kind = ExprKind::kIntegerLiteral;
  hundred->int_val = 100;
  auto* inner_add = f.arena.Create<Expr>();
  inner_add->kind = ExprKind::kBinary;
  inner_add->op = TokenKind::kPlus;
  inner_add->lhs = inner_a;
  inner_add->rhs = hundred;
  auto* inner_assign = f.arena.Create<Stmt>();
  inner_assign->kind = StmtKind::kBlockingAssign;
  inner_assign->lhs = inner_lhs;
  inner_assign->rhs = inner_add;
  inner->func_body_stmts.push_back(inner_assign);
  f.ctx.RegisterFunction("inner", inner);

  auto* outer = f.arena.Create<ModuleItem>();
  outer->kind = ModuleItemKind::kFunctionDecl;
  outer->name = "outer";
  outer->func_args = {
      {Direction::kInput, false, {}, "x", nullptr, {}},
      {Direction::kOutput, false, {}, "y", nullptr, {}},
  };
  auto* call_arg0 = f.arena.Create<Expr>();
  call_arg0->kind = ExprKind::kIdentifier;
  call_arg0->text = "x";
  auto* call_arg1 = f.arena.Create<Expr>();
  call_arg1->kind = ExprKind::kIdentifier;
  call_arg1->text = "y";
  auto* inner_call = f.arena.Create<Expr>();
  inner_call->kind = ExprKind::kCall;
  inner_call->callee = "inner";
  inner_call->args = {call_arg0, call_arg1};
  auto* call_stmt = f.arena.Create<Stmt>();
  call_stmt->kind = StmtKind::kExprStmt;
  call_stmt->expr = inner_call;
  outer->func_body_stmts.push_back(call_stmt);
  f.ctx.RegisterFunction("outer", outer);

  auto* arg0 = f.arena.Create<Expr>();
  arg0->kind = ExprKind::kIntegerLiteral;
  arg0->int_val = 5;
  auto* arg1 = f.arena.Create<Expr>();
  arg1->kind = ExprKind::kIdentifier;
  arg1->text = "result";
  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "outer";
  call->args = {arg0, arg1};

  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(result_var->value.ToUint64(), 105u);
}

}  // namespace
