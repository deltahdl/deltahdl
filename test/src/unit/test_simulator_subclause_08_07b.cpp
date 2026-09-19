#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §8.7's own example, with the values the clause says the properties hold once
// an object of D is constructed: c1 is 1, c2 is 2 because the base constructor
// assigns it after the base properties are initialized, d1 is 4, d2 is 2
// because super.new has completed when the derived properties are initialized,
// and d3 is 6. The clause leaves c3 undefined -- D passes d3 to super.new
// before d3 is initialized -- so c3 is left out of the packed result. The
// five values are packed as one integer so that one comparison holds the
// whole example; a derived level initialized before its base constructor ran
// would read d2 as 1.
TEST(ClassConstructorSim, ClauseExamplePropertiesAfterConstruction) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int c1 = 1;\n"
                      "  int c2 = 1;\n"
                      "  int c3 = 1;\n"
                      "  function new(int a);\n"
                      "    c2 = 2;\n"
                      "    c3 = a;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  int d1 = 4;\n"
                      "  int d2 = c2;\n"
                      "  int d3 = 6;\n"
                      "  function new;\n"
                      "    super.new(d3);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D obj;\n"
                      "    obj = new;\n"
                      "    result = obj.c1 * 10000 + obj.c2 * 1000 +\n"
                      "             obj.d1 * 100 + obj.d2 * 10 + obj.d3;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            12426u);
}

// §8.7 and §8.15: the derived constructor's first statement, super.new(...),
// is the one call of the base class constructor, made with those arguments.
// The base here takes UVM's uvm_component::new shape, telling the root apart
// by the name and null parent the root's constructor passes and counting every
// construction that took the ordinary path. Running the base constructor once
// with no arguments before the derived body and again from the statement left
// the ordinary count at 1 beside the root flag; the one call with "__top__"
// and null leaves it at 0.
TEST(ClassConstructorSim, LeadingSuperNewIsTheOneBaseConstructorCall) {
  EXPECT_EQ(RunAndGet("class base;\n"
                      "  static int ordinary = 0;\n"
                      "  string nm;\n"
                      "  bit is_root = 0;\n"
                      "  function new(string name, base parent);\n"
                      "    nm = name;\n"
                      "    if (parent == null && name == \"__top__\")\n"
                      "      is_root = 1;\n"
                      "    else\n"
                      "      ordinary = ordinary + 1;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class root extends base;\n"
                      "  function new();\n"
                      "    super.new(\"__top__\", null);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    root r;\n"
                      "    r = new;\n"
                      "    result = r.is_root * 100 + base::ordinary * 10 +\n"
                      "             (r.nm == \"__top__\");\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            101u);
}

// §8.7: the base class constructor is called before the derived class's
// properties are initialized, and the rest of the derived constructor body
// runs after them. A derived property whose default reads what the base
// constructor wrote sees that value, and the derived body then reads the
// initialized property; with the base constructor called from the leading
// super.new after the derived properties were initialized, d would have read
// the base default of 1 and y been 1 instead of 9.
TEST(ClassConstructorSim, DerivedBodyRunsAfterItsPropertiesAreInitialized) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  int b = 1;\n"
                      "  function new(int v);\n"
                      "    b = v;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  int d = b;\n"
                      "  int y;\n"
                      "  function new(int v);\n"
                      "    super.new(v);\n"
                      "    y = d;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived obj;\n"
                      "    obj = new(9);\n"
                      "    result = obj.y * 10 + obj.d;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

// §8.7: an object constructed inside a constructor body is built the same
// way, its own base constructor called once from its leading super.new, while
// the outer construction is under way. The outer derived body constructs an
// inner derived object after its own super.new; the inner base counts its
// constructor runs, and each base run stores the argument it was given.
TEST(ClassConstructorSim, ObjectConstructedInsideAConstructorBodyChainsOnce) {
  EXPECT_EQ(
      RunAndGet("class InnerBase;\n"
                "  static int runs = 0;\n"
                "  int v;\n"
                "  function new(int a);\n"
                "    runs = runs + 1;\n"
                "    v = a;\n"
                "  endfunction\n"
                "endclass\n"
                "class Inner extends InnerBase;\n"
                "  function new();\n"
                "    super.new(3);\n"
                "  endfunction\n"
                "endclass\n"
                "class OuterBase;\n"
                "  int w;\n"
                "  function new(int a);\n"
                "    w = a;\n"
                "  endfunction\n"
                "endclass\n"
                "class Outer extends OuterBase;\n"
                "  Inner child;\n"
                "  function new();\n"
                "    super.new(5);\n"
                "    child = new;\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    Outer o;\n"
                "    o = new;\n"
                "    result = o.w * 100 + InnerBase::runs * 10 + o.child.v;\n"
                "  end\n"
                "endmodule\n",
                "result"),
      513u);
}

// §8.15 has super.new be the first statement of the constructor, and A.2.8
// puts a body's local declarations ahead of its statements, so a constructor
// that declares a local before its `super.new("__top__", null)` still makes
// that call its base constructor call -- uvm_root::new's shape, where the
// base takes the root path only for that name. With the declaration counted
// as the first statement the base ran with no arguments and no name.
TEST(ClassConstructorSim, LocalDeclarationAheadOfLeadingSuperNew) {
  EXPECT_EQ(RunAndGet("class base;\n"
                      "  int is_root;\n"
                      "  function new(string name, base parent);\n"
                      "    if (parent == null && name == \"__top__\") "
                      "is_root = 7;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class root extends base;\n"
                      "  int seen;\n"
                      "  extern function new();\n"
                      "endclass\n"
                      "function root::new();\n"
                      "  int scratch;\n"
                      "  super.new(\"__top__\", null);\n"
                      "  scratch = 3;\n"
                      "  seen = scratch;\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    root r;\n"
                      "    r = new;\n"
                      "    result = r.is_root * 10 + r.seen;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            73u);
}

}  // namespace
