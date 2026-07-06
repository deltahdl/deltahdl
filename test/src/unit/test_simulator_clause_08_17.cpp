#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ChainedConstructorSimulation, SuperNewWithArgsInitializesBase) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(int v); x = v; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function new(int v); super.new(v); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d = new(42);\n"
                      "    result = d.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(ChainedConstructorSimulation, ImplicitSuperNewInitializesBase) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 7; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d = new;\n"
                      "    result = d.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(ChainedConstructorSimulation, ThreeLevelChainingEndToEnd) {
  EXPECT_EQ(RunAndGet("class A;\n"
                      "  int a_val;\n"
                      "  function new(); a_val = 1; endfunction\n"
                      "endclass\n"
                      "class B extends A;\n"
                      "  int b_val;\n"
                      "  function new(); super.new(); b_val = 2; endfunction\n"
                      "endclass\n"
                      "class C extends B;\n"
                      "  int c_val;\n"
                      "  function new(); super.new(); c_val = 3; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c = new;\n"
                      "    result = c.a_val + c.b_val * 10 + c.c_val * 100;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            321u);
}

TEST(ChainedConstructorSimulation, BaseConstructorRunsBeforeDerived) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 10; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y;\n"
                      "  function new();\n"
                      "    super.new();\n"
                      "    y = x + 5;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d = new;\n"
                      "    result = d.y;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

TEST(ChainedConstructorSimulation, ImplicitSuperNewWithDerivedConstructor) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x;\n"
                      "  function new(); x = 100; endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y;\n"
                      "  function new(); y = 200; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d = new;\n"
                      "    result = d.x + d.y;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            300u);
}

TEST(ChainedConstructorSimulation, PropertyDefaultsInitializedDuringChaining) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int x = 50;\n"
                      "  function new(); endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int y = 25;\n"
                      "  function new(); super.new(); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d = new;\n"
                      "    result = d.x + d.y;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            75u);
}

// §8.17: the 'default' keyword in the extends specifier expands to the
// superclass constructor's argument list, so a subclass with no explicit
// constructor forwards the new() call's actuals straight to the base
// constructor. Observed end-to-end: the value passed to new() reaches the base
// property.
TEST(ChainedConstructorSimulation, ExtendsDefaultForwardsToBaseConstructor) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base(default);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Der d = new(55);\n"
                      "    result = d.bx;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            55u);
}

// §8.17: 'default' in a subclass constructor's own argument list expands to the
// superclass constructor's arguments, and passing 'default' as the sole
// argument to an explicit super.new() forwards them. The subclass's own
// argument (size) binds from the leading actual; the trailing actual expands
// through 'default' to the base constructor.
TEST(ChainedConstructorSimulation, SuperNewDefaultForwardsExpandedArgs) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base;\n"
                      "  int sz;\n"
                      "  function new(int sz, default);\n"
                      "    super.new(default);\n"
                      "    this.sz = sz;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Der d = new(7, 42);\n"
                      "    result = d.bx + d.sz * 100;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            742u);
}

// §8.17: when a subclass constructor uses 'default' but provides no explicit
// super.new() call, the compiler inserts super.new(default) automatically, so
// the trailing actual still reaches the base constructor.
TEST(ChainedConstructorSimulation,
     ImplicitSuperNewDefaultForwardsExpandedArgs) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base;\n"
                      "  int sz;\n"
                      "  function new(int sz, default);\n"
                      "    this.sz = sz;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Der d = new(3, 99);\n"
                      "    result = d.bx + d.sz * 100;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            399u);
}

// §8.17: a subclass whose extends specifier uses 'default' and that also
// defines its own constructor (repeating 'default') forwards the trailing
// actual to the base while binding its own leading argument locally.
TEST(ChainedConstructorSimulation, ExtendsDefaultWithUserConstructorForwards) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base(default);\n"
                      "  int sz;\n"
                      "  function new(int sz, default);\n"
                      "    this.sz = sz;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Der d = new(4, 88);\n"
                      "    result = d.bx + d.sz * 100;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            488u);
}

// §8.17: 'default' expands to the superclass constructor's argument list in the
// same declaration order. With a two-argument base constructor, the trailing
// actuals must reach the base arguments positionally (a before b), not swapped.
TEST(ChainedConstructorSimulation, DefaultForwardsMultipleArgsInOrder) {
  EXPECT_EQ(
      RunAndGet("class Base;\n"
                "  int ba;\n"
                "  int bb;\n"
                "  function new(int a, int b); ba = a; bb = b; endfunction\n"
                "endclass\n"
                "class Der extends Base;\n"
                "  int sz;\n"
                "  function new(int sz, default);\n"
                "    super.new(default);\n"
                "    this.sz = sz;\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    Der d = new(1, 30, 4);\n"
                "    result = d.ba + d.bb * 10 + d.sz * 100;\n"
                "  end\n"
                "endmodule\n",
                "result"),
      170u);
}

// §8.17: 'default' expands to the superclass constructor's argument list with
// the same DEFAULT VALUES. Here the subclass supplies only the first base
// argument; the second base argument is omitted, so its declared default (30)
// must be applied through the expansion. Observed via the base sum property.
TEST(ChainedConstructorSimulation, ExtendsDefaultAppliesBaseArgDefault) {
  EXPECT_EQ(
      RunAndGet("class Base;\n"
                "  int bx;\n"
                "  function new(int a, int b = 30); bx = a + b; endfunction\n"
                "endclass\n"
                "class Der extends Base(default);\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    Der d = new(7);\n"
                "    result = d.bx;\n"
                "  end\n"
                "endmodule\n",
                "result"),
      37u);
}

// §8.17: when the arguments are given in the extends specifier, the compiler
// inserts the super.new() call automatically. Observed end-to-end: the literal
// argument in 'extends Base(5)' reaches the base constructor at run time even
// though the subclass declares no constructor.
TEST(ChainedConstructorSimulation, ExtendsArgsForwardToBaseConstructor) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int v); bx = v; endfunction\n"
                      "endclass\n"
                      "class Der extends Base(5);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Der d = new;\n"
                      "    result = d.bx;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

// §8.17: the 'default' keyword may appear before the subclass's own added
// arguments (the LRM class-C form: new(default, ...)). The leading actuals then
// expand to the base constructor while the trailing actual binds the subclass's
// own argument.
TEST(ChainedConstructorSimulation, DefaultBeforeOwnArgForwards) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int bx;\n"
                      "  function new(int nv); bx = nv; endfunction\n"
                      "endclass\n"
                      "class Der extends Base;\n"
                      "  bit en;\n"
                      "  function new(default, bit enable);\n"
                      "    super.new(default);\n"
                      "    this.en = enable;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Der d = new(20, 1);\n"
                      "    result = d.bx + d.en * 1000;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1020u);
}

}  // namespace
