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

// §25.10 lets a module take a type from an interface through its port, and
// §6.18 makes the name it declares stand for that type. yes_no is the
// interface's enumeration choice, so P holds its member N and its methods
// answer for the enumeration's two members.
TEST(InterfacePortTypedefSim, TypeTakenThroughAPortIsTheInterfacesType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; typedef enum logic [2:0] {Y=1,N=5} "
                       "choice; endinterface\n"
                       "module sub(ifc i); typedef i.choice yes_no;\n"
                       "  yes_no P = yes_no'(5);\n"
                       "  initial #1 $display(\"n=%s num=%0d\", P.name(), "
                       "P.num());\n"
                       "endmodule\n"
                       "module Top; ifc x(); sub s(x); endmodule\n",
                       f),
            "n=N num=2\n");
}

}  // namespace
