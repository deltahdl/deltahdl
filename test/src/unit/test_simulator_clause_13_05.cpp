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

TEST(SubroutineCallArgWriteback, TaskOutputArgWriteback) {
  // Returning from the subroutine copies the output argument's value back into
  // the caller's variable, observed end to end through the simulator pipeline.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task get_val(output logic [7:0] o);\n"
      "    o = 8'd88;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    get_val(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 88u}});
}

TEST(SubroutineCallArgWriteback, TaskInoutArgRoundTrip) {
  // An inout argument carries the caller's value in and the subroutine's
  // updated value back out on return.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task bump(inout logic [7:0] io);\n"
      "    io = io + 8'd1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 8'd41;\n"
      "    bump(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(SubroutineCallSim, InputArgExpressionEvaluated) {
  // §13.5: an input actual may be any expression; its value is computed at the
  // call site and passed into the formal. Built from real declarations and
  // driven end to end so the value flows through the pipeline.
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] x, a, b;\n"
                      "  function logic [7:0] ident(input logic [7:0] v);\n"
                      "    return v;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    a = 8'd5;\n"
                      "    b = 8'd7;\n"
                      "    x = ident(a + b);\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            12u);
}

TEST(SubroutineCallArgWriteback, PartSelectOutputArgWriteback) {
  // §13.5: the returned output value is written back to the actual. When the
  // actual is a part-select lvalue (§10.4), only the selected bits are updated.
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] x;\n"
                      "  task get(output logic [3:0] o);\n"
                      "    o = 4'hA;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    x = 8'd0;\n"
                      "    get(x[7:4]);\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            0xA0u);
}

TEST(SubroutineCallArgWriteback, StructMemberOutputArgWriteback) {
  // §13.5: the output value is copied back into a member-select actual,
  // updating the corresponding field of the packed struct built from real
  // syntax.
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef struct packed "
                      "{ logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
                      "  pair_t s;\n"
                      "  task get(output logic [3:0] o);\n"
                      "    o = 4'hC;\n"
                      "  endtask\n"
                      "  initial begin\n"
                      "    s = 8'd0;\n"
                      "    get(s.lo);\n"
                      "  end\n"
                      "endmodule\n",
                      "s"),
            0x0Cu);
}

TEST(SubroutineCallArgWriteback, ConcatenationOutputArgWriteback) {
  // §13.5: returning from the subroutine copies the output value back into the
  // actual. When the actual is a concatenation lvalue, the returned value is
  // distributed across the concatenated targets (most-significant slice to the
  // left element), observed end to end through the simulator pipeline.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  task get(output logic [7:0] o);\n"
      "    o = 8'hAB;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 4'd0;\n"
      "    b = 4'd0;\n"
      "    get({a, b});\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 0xAu}, {"b", 0xBu}});
}

}  // namespace
