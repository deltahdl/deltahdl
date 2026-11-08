#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ArgumentBindingSim, VoidFunctionNoParens) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void set_x;\n"
      "    x = 8'd66;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    set_x;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

TEST(ArgumentBindingSim, TaskCallNoParens) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(ArgumentBindingSim, TaskAllDefaultsNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  task set_x(int v = 42);\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 32'd0;\n"
      "    set_x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(ArgumentBindingSim, VoidFunctionAllDefaultsNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void set_x(int v = 99);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 32'd0;\n"
      "    set_x;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 99u}});
}

TEST(ArgumentBindingSim, VoidMethodThroughAHandleNoParens) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 5;\n"
      "  class P;\n"
      "    int a = 3;\n"
      "    function void bump;\n"
      "      a = a * 7 + 2;\n"
      "    endfunction\n"
      "  endclass\n"
      "  P p = new;\n"
      "  initial begin\n"
      "    p.bump;\n"
      "    x = p.a;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 23u);
}

TEST(ArgumentBindingSim,
     VirtualMethodThroughABaseHandleNoParensRunsTheOverride) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 5;\n"
      "  class B;\n"
      "    int r = 0;\n"
      "    virtual function void tag;\n"
      "      r = 11;\n"
      "    endfunction\n"
      "  endclass\n"
      "  class D extends B;\n"
      "    virtual function void tag;\n"
      "      r = 44;\n"
      "    endfunction\n"
      "  endclass\n"
      "  B b;\n"
      "  D d;\n"
      "  initial begin\n"
      "    d = new;\n"
      "    b = d;\n"
      "    b.tag;\n"
      "    x = b.r;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 44u);
}

TEST(ArgumentBindingSim, ClassTaskThroughAHandleNoParensConsumesItsDelay) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 5;\n"
      "  class W;\n"
      "    int v = 0;\n"
      "    task run;\n"
      "      #7;\n"
      "      v = 9;\n"
      "    endtask\n"
      "  endclass\n"
      "  W w = new;\n"
      "  initial begin\n"
      "    w.run;\n"
      "    x = w.v * 100 + $time;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 907u);
}

TEST(ArgumentBindingSim, BareMethodNameInAClassTaskNoParensCallsIt) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 5;\n"
      "  class K;\n"
      "    int n = 0;\n"
      "    function void step;\n"
      "      n = n + 6;\n"
      "    endfunction\n"
      "    task go;\n"
      "      #1;\n"
      "      step;\n"
      "    endtask\n"
      "  endclass\n"
      "  K k = new;\n"
      "  initial begin\n"
      "    k.go();\n"
      "    x = k.n;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 6u);
}

TEST(ArgumentBindingSim, ScopeNamedStaticMethodNoParensReadsItsResult) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    static function int k();\n"
      "      return 41;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int x = 0;\n"
      "  initial x = C::k + 1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

TEST(ArgumentBindingSim, HandleNamedMethodNoParensReadsItsResult) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int n = 7;\n"
      "    function int get();\n"
      "      return n;\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h = new;\n"
      "  int x = 0;\n"
      "  initial x = h.get * 2;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 14u);
}

TEST(ArgumentBindingSim, BareMethodNameReadInAClassMethodCallsIt) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int n = 9;\n"
      "    function int val(int k = 2);\n"
      "      return n * k;\n"
      "    endfunction\n"
      "    function int twice();\n"
      "      return val + 1;\n"
      "    endfunction\n"
      "    static function int base();\n"
      "      return 100;\n"
      "    endfunction\n"
      "    static function int more();\n"
      "      return base + 3;\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h = new;\n"
      "  int x = 0;\n"
      "  initial x = h.twice() + C::more();\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 122u);
}

TEST(ArgumentBindingSim, TypeParameterScopeMethodNoParensReadsItsResult) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    static function int k();\n"
      "      return 41;\n"
      "    endfunction\n"
      "  endclass\n"
      "  class H #(type T = int);\n"
      "    static function int read();\n"
      "      return T::k + 2;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int x = 0;\n"
      "  initial x = H#(C)::read();\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 43u);
}

TEST(ArgumentBindingSim, FunctionNameInsideItsBodyIsItsResultVariable) {
  auto val = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int n = 5;\n"
      "    function int get();\n"
      "      get = 3;\n"
      "      get = get + n;\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h = new;\n"
      "  int x = 0;\n"
      "  initial x = h.get;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 8u);
}

TEST(ArgumentBindingSim, PropertyThroughANullHandleInAGuardIsNoMethodCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class D;\n"
      "  int x;\n"
      "endclass\n"
      "class C;\n"
      "  rand int y;\n"
      "  D a, b;\n"
      "  constraint c1 { (a.x == 5 || b.x > 0) -> y == 10; }\n"
      "endclass\n"
      "module t;\n"
      "  C c;\n"
      "  D d;\n"
      "  int r = 0;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    d = new;\n"
      "    d.x = 5;\n"
      "    c.a = d;\n"
      "    void'(c.randomize());\n"
      "    r = c.y;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ArgumentBindingSim, ScopedAndHierarchicalEnablesNeedNoParentheses) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  int n;\n"
                       "  task t; n = 4; endtask\n"
                       "endpackage\n"
                       "class C;\n"
                       "  static int s;\n"
                       "  static task st; s = 3; endtask\n"
                       "endclass\n"
                       "module dut;\n"
                       "  int a;\n"
                       "  task T2(input int x = 6); a = x; endtask\n"
                       "  function void vf; a = 9; endfunction\n"
                       "endmodule\n"
                       "module top;\n"
                       "  dut d();\n"
                       "  initial begin\n"
                       "    p::t; $display(\"n=%0d\", p::n);\n"
                       "    C::st; $display(\"s=%0d\", C::s);\n"
                       "    d.T2; $display(\"a=%0d\", d.a);\n"
                       "    d.vf; $display(\"a=%0d\", d.a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=4\ns=3\na=6\na=9\n");
}

TEST(ArgumentBindingSim, BareMethodNameInsideItIsTheResultVariable) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "class C;\n"
      "  function int f(int n);\n"
      "    f = 7;\n"
      "    return f + n;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    r = c.f(1);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 8u);
}

}  // namespace
