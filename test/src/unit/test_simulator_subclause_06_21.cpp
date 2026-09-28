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

// §6.21 with §6.8: a variable of an automatic subroutine is created, and its
// initializer run, on every entry to the block declaring it. In the class
// method, `int j = 0;` starts each iteration at 0, so s sums i, 6; kept from
// the iteration before, j accumulated to 0, 1, 3, 6 and s was 10. In the
// automatic function, `int k = 1;` starts at 1, so s sums 1*i, 6 again,
// where a kept k made 1, 2, 6 and 9.
TEST(ScopeAndLifetimeSimulation, AutomaticLoopBodyLocalInitializedEachEntry) {
  const char* src =
      "class N;\n"
      "  function int m();\n"
      "    int s = 0;\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      int j = 0;\n"
      "      j += i;\n"
      "      s += j;\n"
      "    end\n"
      "    return s;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  function automatic int f();\n"
      "    int s = 0, i = 0;\n"
      "    while (i < 3) begin\n"
      "      int k = 1;\n"
      "      i++;\n"
      "      k *= i;\n"
      "      s += k;\n"
      "    end\n"
      "    return s;\n"
      "  endfunction\n"
      "  N n;\n"
      "  int rf, rm;\n"
      "  initial begin\n"
      "    rf = f();\n"
      "    n = new;\n"
      "    rm = n.m();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rf"), 6u);
  EXPECT_EQ(RunAndGet(src, "rm"), 6u);
}

// §6.21 with §9.3.1: a variable declared in an unnamed block is the block's
// own, visible there and in the blocks below it, and hides the module's
// variable of the same name only inside the block. A static, an automatic and
// an uninitialized declaration each write 0 to the block's x, and the
// module's x reads its 1 after each block. Declared as the module's variable
// itself, each block's write reached the module's x.
TEST(ScopeAndLifetimeSimulation, AnUnnamedBlocksVariableLeavesTheModulesAlone) {
  const char* src =
      "module t;\n"
      "  logic x = 1'b1;\n"
      "  logic in_s, out_s, out_a, out_u;\n"
      "  initial begin\n"
      "    begin\n"
      "      static bit x = 1'b0;\n"
      "      in_s = x;\n"
      "    end\n"
      "    out_s = x;\n"
      "    begin\n"
      "      automatic bit x = 1'b0;\n"
      "    end\n"
      "    out_a = x;\n"
      "    begin\n"
      "      bit x;\n"
      "      x = 1'b0;\n"
      "    end\n"
      "    out_u = x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "in_s"), 0u);
  EXPECT_EQ(RunAndGet(src, "out_s"), 1u);
  EXPECT_EQ(RunAndGet(src, "out_a"), 1u);
  EXPECT_EQ(RunAndGet(src, "out_u"), 1u);
}

// §6.21: a variable a block declares without `automatic` in a static process
// is static, one variable kept from one activation of the block to the next.
// The repeat body's acc is set to 0 on the first pass alone and counts the
// passes, so r reads 3; created afresh on each entry, acc read 0 and r 1.
TEST(ScopeAndLifetimeSimulation, AnUnnamedBlocksStaticVariableKeepsItsValue) {
  auto val = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    repeat (3) begin\n"
      "      int acc;\n"
      "      if (r == 0) acc = 0;\n"
      "      acc++;\n"
      "      r = acc;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 3u);
}

}  // namespace
