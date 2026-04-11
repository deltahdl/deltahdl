#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SubroutineCallSim, TaskCallSimple) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd42;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_x();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(SubroutineCallSim, VoidCastFunctionCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function int side_effect;\n"
      "    x = 8'd55;\n"
      "    return 123;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    void'(side_effect());\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 55u}});
}

TEST(SubroutineCallSim, FunctionCallAsStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void set_x;\n"
      "    x = 8'd77;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_x();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(SubroutineCallSim, TaskCallNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd88;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(SubroutineCallSim, SequentialCallStatements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  task set_x;\n"
      "    x = 8'd10;\n"
      "  endtask\n"
      "  task set_y;\n"
      "    y = 8'd20;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    y = 8'd0;\n"
      "    set_x();\n"
      "    set_y();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 10u}, {"y", 20u}});
}

TEST(SubroutineCallSim, FunctionCallReturnValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] get_val();\n"
      "    return 8'd33;\n"
      "  endfunction\n"
      "  initial x = get_val();\n"
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

TEST(SubroutineCallSim, FunctionCallWithArgs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add(logic [7:0] a, logic [7:0] b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  initial x = add(8'd10, 8'd20);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

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

TEST(SubroutineCallSim, TaskInoutArg) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task double_it(inout logic [31:0] v);\n"
      "    v = v * 32'd2;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 32'd7;\n"
      "    double_it(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 14u}});
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

TEST(SubroutineCallArgWriteback, FunctionOutputArgWriteback) {
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

TEST(SubroutineCallSim, TaskCallWithArgs) {
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

TEST(SubroutineCallSim, TaskCallEmptyParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd77;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_x();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(SubroutineCallArgWriteback, NestedFunctionOutputArgs) {
  ExprFixture f;

  auto* result_var = f.ctx.CreateVariable("result", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* inner = f.arena.Create<ModuleItem>();
  inner->kind = ModuleItemKind::kFunctionDecl;
  inner->name = "inner";
  inner->func_args = {
      {Direction::kInput, false, false, {}, "a", nullptr, {}},
      {Direction::kOutput, false, false, {}, "b", nullptr, {}},
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
      {Direction::kInput, false, false, {}, "x", nullptr, {}},
      {Direction::kOutput, false, false, {}, "y", nullptr, {}},
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

TEST(SubroutineCallArgWriteback, FunctionInoutArgWriteback) {
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

TEST(SubroutineCallExprSim, FunctionCallInTernary) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] ten; return 8'd10; endfunction\n"
      "  function logic [7:0] twenty; return 8'd20; endfunction\n"
      "  initial x = 1 ? ten() : twenty();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 10u}});
}

TEST(SubroutineCallSim, FunctionOutputArgEndToEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void compute(input logic [7:0] a, output logic [7:0] b);\n"
      "    b = a * 8'd3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    compute(8'd7, x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 21u}});
}

TEST(SubroutineCallSim, InoutCopyInOut) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void inc(inout logic [7:0] v);\n"
      "    v = v + 8'd1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    inc(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 11u}});
}

}  // namespace
