// §9.2.2.2.1 "Implicit always_comb sensitivities", end to end, for a function
// the block calls by a scoped name: through a hierarchical path of more than
// one instance or from the top module's name, and a class's static method,
// of a class the module or a package declares. A write of what the function
// reads re-runs the block; the line cap in .github/workflows/deltahdl.yml
// separated these from test_simulator_subclause_09_02_02_02_01a.cpp.
#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §9.2.2.2.1 with §23.6: a function two instances down, called as s.t.f(a),
// reads its instance's g, and a write of s.t.g re-runs the block.
TEST(AlwaysCombScopedCallSim, DeeperInstanceFunctionReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n"
                       "  int g;\n"
                       "  function int f(int x); return x + g; endfunction\n"
                       "endmodule\n"
                       "module mid;\n"
                       "  leaf t();\n"
                       "endmodule\n"
                       "module top;\n"
                       "  mid s();\n"
                       "  int a, y;\n"
                       "  always_comb y = s.t.f(a);\n"
                       "  initial begin\n"
                       "    #1 s.t.g = 5;\n"
                       "    #1 $display(\"y=%0d\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "y=5\n");
}

// §9.2.2.2.1 with §23.6: the same function reached by a path from the top
// module's name, top.s.f(a).
TEST(AlwaysCombScopedCallSim, TopRootedPathFunctionReadWakes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  int g;\n"
                       "  function int f(int x); return x + g; endfunction\n"
                       "endmodule\n"
                       "module top;\n"
                       "  sub s();\n"
                       "  int a, y;\n"
                       "  always_comb y = top.s.f(a);\n"
                       "  initial begin\n"
                       "    #1 s.g = 5;\n"
                       "    #1 $display(\"y=%0d\", y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "y=5\n");
}

// §9.2.2.2.1 with §8.23 and §23.9: a class's static method reading a
// variable of the module declaring the class, which a write of re-runs the
// block.
TEST(AlwaysCombScopedCallSim, ClassStaticMethodModuleReadWakes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  int ext;\n"
          "  class C;\n"
          "    static function int f(int x); return x + ext; endfunction\n"
          "  endclass\n"
          "  int a, y;\n"
          "  always_comb y = C::f(a);\n"
          "  initial begin\n"
          "    #1 ext = 5;\n"
          "    #1 $display(\"y=%0d\", y);\n"
          "  end\n"
          "endmodule\n",
          f),
      "y=5\n");
}

// §9.2.2.2.1 with §8.23 and §26.3: a static method of a package's class,
// called as p::C::f(a), reading the class's static property, which a write
// of re-runs the block.
TEST(AlwaysCombScopedCallSim, PackageClassStaticMethodReadWakes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p;\n"
                 "  class C;\n"
                 "    static int g;\n"
                 "    static function int f(int x); return x + g; endfunction\n"
                 "  endclass\n"
                 "endpackage\n"
                 "module t;\n"
                 "  int a, y;\n"
                 "  always_comb y = p::C::f(a);\n"
                 "  initial begin\n"
                 "    #1 p::C::g = 5;\n"
                 "    #1 $display(\"y=%0d\", y);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "y=5\n");
}

}  // namespace
