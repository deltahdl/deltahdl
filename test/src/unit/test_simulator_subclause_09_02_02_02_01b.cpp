#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
