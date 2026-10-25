// End-to-end (parse -> elaborate -> lower -> run) coverage for the §A.4.1.1
// parameter value assignments of a module instance, observed on what the
// instanced module does with the value it is given.

#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A.4.1.1 with A.8.3: a type parameter overridden with a struct type, a
// data_type no expression spells, takes that type, so a variable of the
// parameter's type holds the struct's nine bits (#8066).
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
