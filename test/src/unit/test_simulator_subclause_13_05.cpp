#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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
      "    static C h = new;\n"
      "    h.fill();\n"
      "    r = h.w * 10 + h.z;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 98u);
}

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
      "    static C h = new;\n"
      "    h.fill();\n"
      "    r = h.w;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

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
      "    static D d = new;\n"
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
      "    static A a = new;\n"
      "    r = a.bare() * 10000 + a.qual() * 100 + a.expr();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 484849u);
}

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
      "    static A a = new;\n"
      "    r = a.nested();\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 56u);
}

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
      "    static A a = new;\n"
      "    a.via();\n"
      "    r = a.w;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 48u);
}

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
      "    static A a = new;\n"
      "    a.via();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"aw", 48u}, {"az", 14u}, {"bw", 3u}, {"bz", 5u}});
}

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
      "    static A a = new;\n"
      "    a.via();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"aw", 49u}, {"bw", 48u}, {"cw", 2u}});
}

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

TEST(NestedTagArgumentSim, DISABLED_AnInputFormalKeepsTheInnerTagOfItsActual) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  typedef union tagged {\n"
          "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
          "    union tagged {\n"
          "      bit [9:0] JmpU;\n"
          "      struct { bit [1:0] cc; bit [9:0] addr; } JmpC;\n"
          "    } Jmp;\n"
          "  } Instr;\n"
          "  Instr x, y;\n"
          "  function automatic int fa(input Instr i);\n"
          "    if (i matches tagged Jmp (tagged JmpU .a)) return a; else "
          "return -1;\n"
          "  endfunction\n"
          "  function int fs(input Instr i);\n"
          "    if (i matches tagged Jmp (tagged JmpU .a)) return a; else "
          "return -1;\n"
          "  endfunction\n"
          "  function automatic int fd(input Instr i = tagged Jmp (tagged JmpU "
          "10'd5));\n"
          "    if (i matches tagged Jmp (tagged JmpU .a)) return a; else "
          "return -1;\n"
          "  endfunction\n"
          "  task automatic tk(input Instr i);\n"
          "    y = i;\n"
          "  endtask\n"
          "  class C;\n"
          "    function int m(input Instr i);\n"
          "      if (i matches tagged Jmp (tagged JmpU .a)) return a; else "
          "return -1;\n"
          "    endfunction\n"
          "  endclass\n"
          "  initial begin\n"
          "    C c;\n"
          "    c = new;\n"
          "    x = tagged Jmp (tagged JmpU 10'd100);\n"
          "    $display(\"%0d %0d %0d %0d\", fa(x), fs(x), c.m(x), fd());\n"
          "    $display(\"%0d\", fa(tagged Jmp (tagged JmpU 10'd7)));\n"
          "    tk(x);\n"
          "    if (y matches tagged Jmp (tagged JmpU .a)) $display(\"copy "
          "%0d\", a);\n"
          "    else $display(\"copy lost\");\n"
          "  end\n"
          "endmodule\n",
          f),
      "100 100 100 5\n7\ncopy 100\n");
}

TEST(NestedTagArgumentSim,
     DISABLED_RefAndInoutFormalsKeepTheInnerTagOfTheActual) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged {\n"
                       "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                       "    union tagged {\n"
                       "      bit [9:0] JmpU;\n"
                       "      struct { bit [1:0] cc; bit [9:0] addr; } JmpC;\n"
                       "    } Jmp;\n"
                       "  } Instr;\n"
                       "  Instr x, y;\n"
                       "  function automatic int fr(ref Instr i);\n"
                       "    if (i matches tagged Jmp (tagged JmpC '{.c, .a})) "
                       "return c * 1000 + a;\n"
                       "    else return -1;\n"
                       "  endfunction\n"
                       "  task automatic tio(inout Instr i);\n"
                       "    if (i matches tagged Jmp (tagged JmpC '{.c, .a})) "
                       "$display(\"inout %0d %0d\", c, a);\n"
                       "    else $display(\"inout lost\");\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    x = tagged Jmp (tagged JmpC '{2'd2, 10'd7});\n"
                       "    $display(\"ref %0d\", fr(x));\n"
                       "    tio(x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ref 2007\ninout 2 7\n");
}

TEST(NestedTagArgumentSim,
     DISABLED_OutputFormalsAndReturnValuesKeepTheInnerTag) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged {\n"
                       "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                       "    union tagged {\n"
                       "      bit [9:0] JmpU;\n"
                       "      struct { bit [1:0] cc; bit [9:0] addr; } JmpC;\n"
                       "    } Jmp;\n"
                       "  } Instr;\n"
                       "  Instr x, y;\n"
                       "  function automatic Instr mk(input bit [9:0] v);\n"
                       "    return tagged Jmp (tagged JmpU v);\n"
                       "  endfunction\n"
                       "  task automatic out(output Instr o);\n"
                       "    o = tagged Jmp (tagged JmpC '{2'd1, 10'd33});\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    x = mk(10'd44);\n"
                       "    if (x matches tagged Jmp (tagged JmpU .a)) "
                       "$display(\"return %0d\", a);\n"
                       "    else $display(\"return lost\");\n"
                       "    out(y);\n"
                       "    if (y matches tagged Jmp (tagged JmpC '{.c, .a})) "
                       "$display(\"output %0d %0d\", c, a);\n"
                       "    else $display(\"output lost\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "return 44\noutput 1 33\n");
}

}  // namespace
