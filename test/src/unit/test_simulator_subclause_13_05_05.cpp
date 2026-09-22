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

// §13.5.5 (printed page 351): the empty parentheses after the name of a class
// function method with no arguments are optional, so the statement `p.bump;`
// is the call `p.bump();`, and §8.6 (printed 183) has a method reached
// through the handle of the object it belongs to. The statement was evaluated
// as a read of a property called bump and the method never ran, so a read
// after it gave 3, the property's initial value, rather than the 23 the
// method leaves.
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

// §13.5.5 with §8.20 (printed page 196): the parenthesis-free call goes to
// the same method the parenthesised one does, so a virtual method named
// through a base-class handle runs the override of the object's class -- the
// example of §8.20 writes every one of its calls this way. The base method
// writes 11, the override 44, and a call that never ran leaves 0.
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

// §13.5.5 makes the parentheses optional for a task too, and §13.3 (printed
// page 335) has control return to the enabling process only when the task
// has completed, so a class task with a delay called as `w.run;` suspends
// the caller for the delay as `w.run();` does: the write the task makes is
// seen after it, and $time read after the call is the task's 7, not the 0 of
// a call run through the function interpreter with its delay skipped.
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

// §13.5.5 with §8.13 (printed page 190): a method of the running object named
// by its bare name inside another of its methods is a call as `step();` is,
// so a class task calling `step;` runs it on the same object. The step writes
// 6 into the counter it finds at 0; a bare name read as a variable instead
// leaves it at 0.
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

// §13.5.5 (printed page 351): the parentheses are optional after a class
// function method with no arguments wherever it is called, so `C::k` read as
// an operand is the call `C::k()`. The call answers 41 and the sum 42; the
// name read as a static property of the class instead answers nothing.
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

// §13.5.5 with §8.6: `h.get` read as an operand is `h.get()`, run on the
// object the handle holds, whose n is 7.
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

// §13.5.5 with §8.13: inside a method of the class, the bare name of another
// read as an operand is its call, the formal with a default included, and in
// a static method a static method's bare name is (§8.10).
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

// §13.5.5 with §8.25 (printed page 204): `T::k` through a type parameter is
// the call of k on the class the parameter's actual names.
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

// §13.5.5 with §13.4.1 (printed page 342): inside a nonvoid function its own
// name is the variable holding its result, never a call of the function, so
// `get` reads the 3 written to it and the function answers 3 + 5.
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

}  // namespace
