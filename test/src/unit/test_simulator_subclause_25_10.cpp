#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §25.10: an interface's variables are reached by hierarchical name, and a
// continuous assignment reading one, `assign w = dif.d;`, is sensitive to it
// as to any variable it reads (§10.3.2), so w follows dif.d's change to 1.
// Its reads were collected as the two names `dif` and `d`, neither a variable,
// and the assignment ran once and never again.
TEST(InterfaceObjectAccess, ContinuousAssignmentFollowsAnInterfaceMember) {
  SimFixture f;
  auto out = RunCapture(
      "interface gi;\n"
      "  logic d;\n"
      "endinterface\n"
      "module t;\n"
      "  gi dif();\n"
      "  wire w;\n"
      "  assign w = dif.d;\n"
      "  initial begin\n"
      "    dif.d = 0;\n"
      "    #10 dif.d = 1;\n"
      "    #1 $display(\"%0d\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

// The same for always_comb, whose implicit sensitivity is the variables it
// reads (§9.2.2.2.1): it reruns when dif.d changes, so c counts both values.
TEST(InterfaceObjectAccess, AlwaysCombRerunsOnAnInterfaceMember) {
  SimFixture f;
  auto out = RunCapture(
      "interface gi;\n"
      "  logic d;\n"
      "endinterface\n"
      "module t;\n"
      "  gi dif();\n"
      "  logic q;\n"
      "  always_comb q = dif.d;\n"
      "  initial begin\n"
      "    dif.d = 0;\n"
      "    #10 dif.d = 1;\n"
      "    #1 $display(\"%0d\", q);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

}  // namespace
