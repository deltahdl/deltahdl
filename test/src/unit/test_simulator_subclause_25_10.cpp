#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
