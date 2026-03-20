#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SubroutineCallSim, NestedFunctionCalls) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] double_val(input logic [7:0] v);\n"
      "    return v * 8'd2;\n"
      "  endfunction\n"
      "  function logic [7:0] quad_val(input logic [7:0] v);\n"
      "    return double_val(double_val(v));\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = quad_val(8'd3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(SubroutineCallSim, TaskOutputArg) {
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

TEST(SubroutineCallExprSim, FunctionCallInBinaryExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] five; return 8'd5; endfunction\n"
      "  function logic [7:0] three; return 8'd3; endfunction\n"
      "  initial x = five() + three();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(Eval, FunctionOutputArgWriteback) {
  ExprFixture f;

  auto* result_var = f.ctx.CreateVariable("result", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "compute";
  func->func_args = {
      {Direction::kInput, false, false, {}, "a", nullptr, {}},
      {Direction::kOutput, false, false, {}, "b", nullptr, {}},
  };

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "b";

  auto* a_ref = f.arena.Create<Expr>();
  a_ref->kind = ExprKind::kIdentifier;
  a_ref->text = "a";

  auto* two = f.arena.Create<Expr>();
  two->kind = ExprKind::kIntegerLiteral;
  two->int_val = 2;

  auto* mul = f.arena.Create<Expr>();
  mul->kind = ExprKind::kBinary;
  mul->op = TokenKind::kStar;
  mul->lhs = a_ref;
  mul->rhs = two;

  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = mul;
  func->func_body_stmts.push_back(assign);

  f.ctx.RegisterFunction("compute", func);

  auto* arg0 = f.arena.Create<Expr>();
  arg0->kind = ExprKind::kIntegerLiteral;
  arg0->int_val = 21;

  auto* arg1 = f.arena.Create<Expr>();
  arg1->kind = ExprKind::kIdentifier;
  arg1->text = "result";

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "compute";
  call->args = {arg0, arg1};

  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

TEST(Eval, FunctionInoutArgWriteback) {
  ExprFixture f;

  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "increment";
  func->func_args = {{Direction::kInout, false, false, {}, "v", nullptr, {}}};

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "v";

  auto* v_ref = f.arena.Create<Expr>();
  v_ref->kind = ExprKind::kIdentifier;
  v_ref->text = "v";

  auto* one = f.arena.Create<Expr>();
  one->kind = ExprKind::kIntegerLiteral;
  one->int_val = 1;

  auto* add = f.arena.Create<Expr>();
  add->kind = ExprKind::kBinary;
  add->op = TokenKind::kPlus;
  add->lhs = v_ref;
  add->rhs = one;

  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = add;
  func->func_body_stmts.push_back(assign);

  f.ctx.RegisterFunction("increment", func);

  auto* arg = f.arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = "x";

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "increment";
  call->args = {arg};

  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(x_var->value.ToUint64(), 11u);
}

}  // namespace
