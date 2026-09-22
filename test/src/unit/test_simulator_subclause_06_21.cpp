#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ScopeAndLifetimeSimulation, ExplicitStaticInAutoFuncBlockPersists) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int get_id();\n"
      "    begin\n"
      "      static int next_id = 0;\n"
      "      next_id = next_id + 1;\n"
      "      return next_id;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "    result = get_id();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, ExplicitAutoInStaticFuncBlockFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function static int get_val();\n"
      "    begin\n"
      "      automatic int temp = 10;\n"
      "      temp = temp + 1;\n"
      "      return temp;\n"
      "    end\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = get_val();\n"
      "    result = get_val();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 11u);
}

TEST(ScopeAndLifetimeSimulation, ForLoopVarHasLocalScope) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 100;\n"
      "    for (int x = 0; x < 5; x = x + 1) begin\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 100u);
}

TEST(ScopeAndLifetimeSimulation, StaticFunctionVarsPersist) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function static int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

TEST(ScopeAndLifetimeSimulation, AutomaticFunctionVarsFresh) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function automatic int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(ScopeAndLifetimeSimulation, DefaultFunctionIsStatic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

TEST(ScopeAndLifetimeSimulation, DefaultLifetimeInAutoModuleIsAutomatic) {
  auto val = RunAndGet(
      "module automatic t;\n"
      "  logic [31:0] result;\n"
      "  function int counter();\n"
      "    int cnt;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "    result = counter();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

TEST(ScopeAndLifetimeSimulation, UnnamedBlockVarVisibleToNestedBlock) {
  // §6.21: a variable declared in an unnamed block is visible both to that
  // block and to any nested block below it. Here `outer` is declared in the
  // initial block and then read and written from an inner unnamed block; the
  // write must land on that same variable, so the enclosing block observes 15
  // (5 + 10), not the original 5.
  auto val = RunAndGet(
      "module t;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    int outer = 5;\n"
      "    begin\n"
      "      outer = outer + 10;\n"
      "    end\n"
      "    observed = outer;\n"
      "  end\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 15u);
}

// §6.21: a variable explicitly declared static inside an automatic function
// has a static lifetime, one copy kept between calls, and that copy is the
// function's own -- §13.4.2 has a static subroutine's items belong to the
// subroutine that declares them. Two classes each declaring a static method
// bump() with a static local n are two functions and two copies. Two calls to
// A::bump() and one to B::bump() discriminate: one copy under the name bump
// reads 3 for B's call, and a copy each reads 1.
TEST(ScopeAndLifetimeSimulation,
     StaticLocalOfOneClassMethodIsNotAnotherClasss) {
  auto val = RunAndGet(
      "module t;\n"
      "  class A;\n"
      "    static function int bump(); static int n; n++; return n;\n"
      "    endfunction\n"
      "  endclass\n"
      "  class B;\n"
      "    static function int bump(); static int n; n++; return n;\n"
      "    endfunction\n"
      "  endclass\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    void'(A::bump());\n"
      "    void'(A::bump());\n"
      "    result = B::bump();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 1u);
}

}  // namespace
