#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(TypeParameterPortSimulation, ANamedOverrideRetypesOnlyItsInstancesPort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter type T = int)(input var T a);\n"
                       "  initial #1 $display(\"%m %0d\", $bits(a));\n"
                       "endmodule\n"
                       "module t;\n"
                       "  byte b1;\n"
                       "  int b2;\n"
                       "  m #(.T(byte)) u(b1);\n"
                       "  m v(b2);\n"
                       "endmodule\n",
                       f),
            "t.u 8\nt.v 32\n");
}

TEST(TypeParameterPortSimulation, APositionalOverrideRetypesThePort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter type T = int)(input var T a);\n"
                       "  initial #1 $display(\"%0d\", $bits(a));\n"
                       "endmodule\n"
                       "module t;\n"
                       "  shortint s;\n"
                       "  m #(shortint) u(s);\n"
                       "endmodule\n",
                       f),
            "16\n");
}

TEST(TypeParameterPortSimulation,
     DISABLED_TheRetypedPortKeepsTheSignednessOfItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter type T = int)(input var T a);\n"
                       "  initial #1 $display(\"%0d\", a);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  byte b = -5;\n"
                       "  m #(.T(byte)) u(b);\n"
                       "endmodule\n",
                       f),
            "-5\n");
}

TEST(TypeParameterPortSimulation, AnInterfacePortTakesTheOverridingType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface i #(parameter type T = int)(input var T a);\n"
                       "  initial #1 $display(\"%0d\", $bits(a));\n"
                       "endinterface\n"
                       "module t;\n"
                       "  byte b;\n"
                       "  i #(.T(byte)) u(b);\n"
                       "endmodule\n",
                       f),
            "8\n");
}

TEST(TypeParameterPortSimulation,
     DISABLED_TheDefaultTypedPortKeepsTheSignednessOfItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter type T = int)(input var T a);\n"
                       "  initial #1 $display(\"%0d\", a);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  int b = -5;\n"
                       "  m u(b);\n"
                       "endmodule\n",
                       f),
            "-5\n");
}

TEST(TypeParameterPortSimulation, AnExplicitlyTypedPortKeepsItsSignedness) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m(input var byte a);\n"
                       "  initial #1 $display(\"%0d\", a);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  byte b = -5;\n"
                       "  m u(b);\n"
                       "endmodule\n",
                       f),
            "-5\n");
}

}  // namespace
