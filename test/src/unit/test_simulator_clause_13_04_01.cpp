#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(FunctionReturnSim, VoidFunctionReturnsZero) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "set_val";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {{Direction::kInput, false, false, false, {}, "a", nullptr, {}}};
  f.ctx.RegisterFunction("set_val", func);

  auto* call = MakeCall(f.arena, "set_val", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(FunctionReturnSim, ReturnStatementFromFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function int get_val();\n"
      "    return 42;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = get_val();\n"
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

TEST(FunctionReturnSim, FunctionReturnValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add_one(input logic [7:0] v);\n"
      "    return v + 8'd1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = add_one(8'd9);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(FunctionReturnSim, NestedFunctionCalls) {
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
      "  initial x = quad_val(8'd3);\n"
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

TEST(FunctionReturnSim, FunctionNameAssignReturnsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  function logic [15:0] myfunc1(input logic [7:0] a, input logic [7:0] "
      "b);\n"
      "    myfunc1 = a * b - 16'd1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = myfunc1(8'd3, 8'd5);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 14u}});
}

TEST(FunctionReturnSim, ReturnOverridesFunctionNameAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int compute();\n"
      "    compute = 100;\n"
      "    return 42;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = compute();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(FunctionReturnSim, EmptyFunctionReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int nop();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = nop();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(FunctionReturnSim, FunctionNameAssignConditional) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int abs_val(input int v);\n"
      "    if (v < 0)\n"
      "      abs_val = -v;\n"
      "    else\n"
      "      abs_val = v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = abs_val(32'd7);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}});
}

TEST(FunctionReturnSim, NonvoidFunctionAsOperandInExpr) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] five; return 32'd5; endfunction\n"
      "  initial x = five() + 32'd3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 8u);
}

TEST(FunctionReturnSim, VoidFunctionSideEffect) {
  FuncFixture f;

  auto* g_var = f.ctx.CreateVariable("g", 32);
  g_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "store";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kOutput, false, false, false, {}, "out", nullptr, {}}};
  func->func_body_stmts.push_back(
      MakeAssign(f.arena, "out", MakeInt(f.arena, 99)));
  f.ctx.RegisterFunction("store", func);

  auto* call = MakeCall(f.arena, "store", {MakeId(f.arena, "g")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(g_var->value.ToUint64(), 99u);
}

TEST(FunctionReturnSim, VoidFunctionBareReturnExitsEarly) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void set_x(output logic [31:0] v);\n"
      "    v = 32'd10;\n"
      "    return;\n"
      "    v = 32'd99;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    set_x(x);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 10u);
}

TEST(FunctionReturnSim, BareReturnUsesImplicitVar) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int compute(input int a);\n"
      "    compute = a * 3;\n"
      "    return;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = compute(5);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 15u}});
}

TEST(FunctionReturnSim, MultipleFunctionNameAssignsLastWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int pick();\n"
      "    pick = 32'd1;\n"
      "    pick = 32'd2;\n"
      "    pick = 32'd3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = pick();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 3u}});
}

TEST(FunctionReturnSim, FunctionNameAssignRespectsReturnWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  function logic [3:0] narrow();\n"
      "    narrow = 8'hFF;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = narrow();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 15u}});
}

}  // namespace
