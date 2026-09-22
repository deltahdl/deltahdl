#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
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

// §13.5 (printed page 348) has the return from a subroutine pass the value of
// an output formal to the variable the call named as the actual, and §8.11
// (printed 187) makes `this.w` inside a method the property `w` of the object
// the method was invoked on -- the same target the bare `w` names, spelled
// with its handle. The copy-out resolves that actual with the caller's `this`
// and the caller's class in force, so it lands where a read through the handle
// looks: `h.w` reads the property under the key the object's construction
// wrote for the declaring class, and a deposit under the bare key alone
// answered the stale 0 beside it. w takes 9 through `setw(this.w)` and z 9
// through `setw(z)` less one, so the read is 98; the copy-out dropped for the
// `this.`-spelled actual alone gave 8.
TEST(SubroutineCallArgWriteback,
     OutputActualThisPropertyInsideAMethodIsWrittenAtReturn) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int w, z;\n"
      "    function void fill();\n"
      "      setw(this.w);\n"
      "      setw(z);\n"
      "      z = z - 1;\n"
      "    endfunction\n"
      "    function void setw(output int o);\n"
      "      o = 9;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r;\n"
      "  initial begin\n"
      "    C h = new;\n"
      "    h.fill();\n"
      "    r = h.w * 10 + h.z;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 98u);
}

// The inout form of the same actual: §13.5 passes the actual's value in at the
// call and the formal's value out at the return, so `bump(this.w)` with w at 3
// reads 3 into the formal, adds 4, and writes 7 back to the property. A
// copy-out that missed the `this.`-spelled actual left 3; a copy-in that read
// the property as 0 left 4.
TEST(SubroutineCallArgWriteback,
     InoutActualThisPropertyInsideAMethodIsReadAndWrittenBack) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int w;\n"
      "    function void fill();\n"
      "      this.w = 3;\n"
      "      bump(this.w);\n"
      "    endfunction\n"
      "    function void bump(inout int o);\n"
      "      o = o + 4;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r;\n"
      "  initial begin\n"
      "    C h = new;\n"
      "    h.fill();\n"
      "    r = h.w;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §8.15 has a method of the base class name the base's declaration of `w`
// through `this.w` whatever the object's own class, so a `fill` declared in B
// and invoked on a D object writes the `w` B declares, and a read through the
// D-typed handle and through a B-typed one both see it: 9 * 100 + 9 = 909. The
// copy-out dropped on the derived object gave 0.
TEST(SubroutineCallArgWriteback,
     OutputActualThisPropertyFromABaseMethodOnADerivedObject) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class B;\n"
      "    int w;\n"
      "    function void fill();\n"
      "      setw(this.w);\n"
      "    endfunction\n"
      "    function void setw(output int o);\n"
      "      o = 9;\n"
      "    endfunction\n"
      "  endclass\n"
      "  class D extends B;\n"
      "    int extra;\n"
      "  endclass\n"
      "  int r;\n"
      "  initial begin\n"
      "    D d = new;\n"
      "    B b;\n"
      "    b = d;\n"
      "    d.fill();\n"
      "    r = d.w * 100 + b.w;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 909u);
}

// §13.5 (printed page 348) has the call pass an input formal the value of
// the expression written in the call, and §8.11 (printed page 187) makes a
// property named inside a method, bare or as `this.v`, the property of the
// object the method was invoked on. `b.add8(v)` inside a method of A, with
// A's `v` at 40, therefore passes 40 and reads 48; the actual read with B's
// object already in force found no `v` on it and passed 0, so the method
// answered 8. Bare, `this.`-qualified and the expression `v + 1` are read
// into one number: 48 * 10000 + 48 * 100 + 49 = 484849 against 80809.
TEST(SubroutineCallSim, ActualNamingAPropertyOfTheCallingObject) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class B;\n"
      "    function int add8(int a); return a + 8; endfunction\n"
      "  endclass\n"
      "  class A;\n"
      "    int v = 40;\n"
      "    function int bare(); B b = new; return b.add8(v); endfunction\n"
      "    function int qual(); B b = new; return b.add8(this.v);\n"
      "    endfunction\n"
      "    function int expr(); B b = new; return b.add8(v + 1);\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r;\n"
      "  initial begin\n"
      "    A a = new;\n"
      "    r = a.bare() * 10000 + a.qual() * 100 + a.expr();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 484849u);
}

// The same rule one call deeper: in `b.add8(c.add8(v))` the inner call is an
// actual of the outer one and `v` an actual of the inner one, both written
// in A's method, so both are read on A's object: 40 + 8 + 8 = 56. A read on
// the wrong object gave 16. The inner call's own object is pushed while its
// actual is read, so a bind that set only the outermost callee aside would
// still fail here.
TEST(SubroutineCallSim, ActualNamingAPropertyOfTheCallingObjectInANestedCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class B;\n"
      "    function int add8(int a); return a + 8; endfunction\n"
      "  endclass\n"
      "  class A;\n"
      "    int v = 40;\n"
      "    function int nested();\n"
      "      B b = new; B c = new;\n"
      "      return b.add8(c.add8(v));\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r;\n"
      "  initial begin\n"
      "    A a = new;\n"
      "    r = a.nested();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 56u);
}

// A class task enabled on another object takes the same rule: §13.5 reads
// the actual in the enabling task, so `b.addt(v, t)` inside a task of A
// passes A's 40 and B's task answers 48 through the output formal, which the
// enabling task keeps in A's `w`; with B's object in force for the actual it
// answered 8.
TEST(SubroutineCallSim, TaskActualNamingAPropertyOfTheCallingObject) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class B;\n"
      "    task addt(input int a, output int o); o = a + 8; endtask\n"
      "  endclass\n"
      "  class A;\n"
      "    int v = 40;\n"
      "    int w;\n"
      "    task via(); B b = new; int t; b.addt(v, t); w = t; endtask\n"
      "  endclass\n"
      "  int r;\n"
      "  initial begin\n"
      "    A a = new;\n"
      "    a.via();\n"
      "    r = a.w;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 48u);
}

// §13.5 (printed page 348) copies an output or inout formal to its actual
// when the task returns, and the actual is written in the enabling method,
// so by §8.11 (printed 187) a property it names is the enabling object's:
// `b.addt(v, w)` and `b.dbl(z)` in a task of A leave 48 in A's `w` and 14 in
// A's `z`, and B's `w` and `z` -- the same names, so a copy-out on the wrong
// object shows as their change -- keep 3 and 5. With B's object still in
// force for the copy-out, A's kept 1 and 7 while B's took 48 and 14.
TEST(SubroutineCallSim, TaskOutputActualNamingAPropertyOfTheCallingObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aw, az, bw, bz;\n"
      "  class B;\n"
      "    int w = 3;\n"
      "    int z = 5;\n"
      "    task addt(input int a, output int o); o = a + 8; endtask\n"
      "    task dbl(inout int io); io = io * 2; endtask\n"
      "  endclass\n"
      "  class A;\n"
      "    int v = 40;\n"
      "    int w = 1;\n"
      "    int z = 7;\n"
      "    task via();\n"
      "      B b = new;\n"
      "      b.addt(v, w);\n"
      "      b.dbl(z);\n"
      "      aw = w; az = z; bw = b.w; bz = b.z;\n"
      "    endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    A a = new;\n"
      "    a.via();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"aw", 48u}, {"az", 14u}, {"bw", 3u}, {"bz", 5u}});
}

// The same rule one enable deeper: B's task `outer`, enabled from A's,
// enables C's `addt` with B's own `w` as the output actual, so the copy-out
// lands on B's object (48), `outer` answers 49 into A's `w`, and C's `w`
// keeps 2. With the enabled task's object still in force for each copy-out,
// C's `w` took 48, B's took 4 and A's kept 1.
TEST(SubroutineCallSim, TaskOutputActualOfANestedTaskNamingTheEnablingObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aw, bw, cw;\n"
      "  class C;\n"
      "    int w = 2;\n"
      "    task addt(input int a, output int o); o = a + 8; endtask\n"
      "  endclass\n"
      "  class B;\n"
      "    int w = 3;\n"
      "    task outer(input int a, output int o);\n"
      "      C c = new;\n"
      "      c.addt(a, w);\n"
      "      o = w + 1;\n"
      "      bw = w; cw = c.w;\n"
      "    endtask\n"
      "  endclass\n"
      "  class A;\n"
      "    int v = 40;\n"
      "    int w = 1;\n"
      "    task via(); B b = new; b.outer(v, w); aw = w; endtask\n"
      "  endclass\n"
      "  initial begin\n"
      "    A a = new;\n"
      "    a.via();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"aw", 49u}, {"bw", 48u}, {"cw", 2u}});
}

// §13.5 (printed page 348) has the call pass an input formal the value of
// the expression written in the call, and §8.10 (printed page 186) runs a
// static method in its class's scope, which each call pushes before binding
// the actuals. `n` written in a static method of A is A's static n, 20, so
// K::twice(n) answers 40, P#(3)::plus(n) 23 and k.twice(n) 40; read with
// the callee's class in force each found the callee's own n, 5 or 7, and
// answered 101010.
TEST(SubroutineCallSim, ActualOfAStaticCallReadInTheCallersClass) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class K;\n"
      "    static int n = 5;\n"
      "    static function int twice(int a); return a * 2; endfunction\n"
      "  endclass\n"
      "  class P #(int W = 1);\n"
      "    static int n = 7;\n"
      "    static function int plus(int a); return a + W; endfunction\n"
      "  endclass\n"
      "  class A;\n"
      "    static int n = 20;\n"
      "    static function int scope(); return K::twice(n); endfunction\n"
      "    static function int spec(); return P#(3)::plus(n); endfunction\n"
      "    static function int handle(); K k = new; return k.twice(n);\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r;\n"
      "  initial r = A::scope() * 10000 + A::spec() * 100 + A::handle();\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 402340u);
}

// §13.5 with §8.23 (printed page 200): the scope an actual names is looked
// up where the call is written, so `K::chk(T::get())` in `H #(type T)`
// passes the handle R::get() returns under H#(R), whose v K::chk reads as 7.
// Read under K, which has no T, the actual was the null handle and chk
// answered -1.
TEST(SubroutineCallSim, ActualNamingATypeParameterOfTheCallersClass) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class R;\n"
      "    int v = 7;\n"
      "    static function R get(); R r = new; return r; endfunction\n"
      "  endclass\n"
      "  class K;\n"
      "    static function int chk(R x); return x == null ? -1 : x.v;\n"
      "    endfunction\n"
      "  endclass\n"
      "  class H #(type T = int);\n"
      "    static function int go(); return K::chk(T::get()); endfunction\n"
      "  endclass\n"
      "  int r;\n"
      "  initial r = H#(R)::go();\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §13.5 with §8.10: a static task pushes its class before binding the
// actuals as a static function does, so `K::twice(n)` in a static task of A
// passes A's n, 20, and stores 40; read under K it passed K's 5 and stored
// 10.
TEST(SubroutineCallSim, ActualOfAStaticTaskCallReadInTheCallersClass) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r;\n"
      "  class K;\n"
      "    static int n = 5;\n"
      "    static task twice(input int a); r = a * 2; endtask\n"
      "  endclass\n"
      "  class A;\n"
      "    static int n = 20;\n"
      "    static task via(); K::twice(n); endtask\n"
      "  endclass\n"
      "  initial A::via();\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 40u);
}

}  // namespace
