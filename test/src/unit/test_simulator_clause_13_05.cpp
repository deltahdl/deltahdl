// §13.5: Subroutine calls and argument passing

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// Simulation tests — A.6.9 Subroutine call statements
// =============================================================================
// --- tf_call: task call ---
// Simple task call modifies a variable
TEST(SimA609, TaskCallSimple) {
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

// --- void'(function_subroutine_call) ---
TEST(SimA609, VoidCastFunctionCall) {
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

// --- nested function calls ---
TEST(SimA609, NestedFunctionCalls) {
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

// --- task with output argument ---
TEST(SimA609, TaskOutputArg) {
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

// § tf_call — task call modifies variable
TEST(SimA82, TfCallTaskModifiesVar) {
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

// § tf_call — function call in expression with binary op
TEST(SimA82, FunctionCallInBinaryExpr) {
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

// =============================================================================
// Function output argument writeback
// =============================================================================
TEST(Eval, FunctionOutputArgWriteback) {
  ExprFixture f;

  // Create variable "result" in global scope.
  auto* result_var = f.ctx.CreateVariable("result", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  // Build function: function void compute(input int a, output int b);
  //   b = a * 2;
  // endfunction
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "compute";
  func->func_args = {
      {Direction::kInput, false, {}, "a", nullptr, {}},
      {Direction::kOutput, false, {}, "b", nullptr, {}},
  };

  // Body: b = a * 2
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

  // Build call expression: compute(21, result)
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

  // Output arg "b" should have been written back to "result".
  EXPECT_EQ(result_var->value.ToUint64(), 42u);
}

}  // namespace
