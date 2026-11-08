#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ParameterValueAssignmentSim, ATypeParameterTakesAStructType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub #(parameter type T = int) ();\n"
                       "  T v;\n"
                       "  initial $display(\"%0d\", $bits(v));\n"
                       "endmodule\n"
                       "module t;\n"
                       "  sub #(.T(struct packed { bit a; byte b; })) u();\n"
                       "endmodule\n",
                       f),
            "9\n");
}

}  // namespace
