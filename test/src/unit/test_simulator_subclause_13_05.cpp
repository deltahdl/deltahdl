#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SubroutineCallSim, TaskCallSimple) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
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
  auto* var = RunAndFindVar(
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
      f, "x");
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] get_val();\n"
      "    return 8'd33;\n"
      "  endfunction\n"
      "  initial x = get_val();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(SubroutineCallSim, FunctionCallWithArgs) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add(logic [7:0] a, logic [7:0] b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  initial x = add(8'd10, 8'd20);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(SubroutineCallSim, NestedFunctionCalls) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(SubroutineCallExprSim, FunctionCallInBinaryExpr) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] five; return 8'd5; endfunction\n"
      "  function logic [7:0] three; return 8'd3; endfunction\n"
      "  initial x = five() + three();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(SubroutineCallSim, TaskCallWithArgs) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
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

// §13.5: an actual is an expression of the caller, read before the formal it
// is passed to exists. §13.3.2 gives a static function's formal storage that
// retains the last call's value, so an actual named after the formal must not
// read that retained value: the second call of twice(k) reads the module's k
// at 7, not the formal's retained 3, and sums to 20. Read from the formal,
// the second call would repeat the first and the sum would be 12.
TEST(SubroutineCallSim, ActualNamedAfterAStaticFormalReadsTheCallersVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int k, sum;\n"
      "  function int twice(input int k);\n"
      "    return 2 * k;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    k = 3;\n"
      "    sum = twice(k);\n"
      "    k = 7;\n"
      "    sum = sum + twice(k);\n"
      "  end\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// The same rule between the formals of one call: an actual named after a
// formal bound before it reads the caller's variable of that name, not the
// formal just bound. diff(b, a) with the module's a at 10 and b at 4 binds the
// formal a to 4 and then the formal b to the caller's a, 10, and answers 4 -
// 10 as -6; read from the formal a, b would be 4 and the answer 0.
TEST(SubroutineCallSim,
     ActualNamedAfterAnEarlierFormalReadsTheCallersVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a, b, d;\n"
      "  function int diff(input int a, input int b);\n"
      "    return a - b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 4;\n"
      "    d = diff(b, a);\n"
      "  end\n"
      "endmodule\n",
      f, "d");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(static_cast<int32_t>(var->value.ToUint64()), -6);
}

}  // namespace
