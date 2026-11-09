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

TEST(InterfacePortTypedefSim,
     TypeTakenThroughAPortArrayElementGainsNoDimension) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  typedef byte IT;\n"
                       "  typedef byte IA [3];\n"
                       "endinterface\n"
                       "module sub(ifc i [2]);\n"
                       "  typedef i[1].IT T;\n"
                       "  typedef i[0].IA A;\n"
                       "  T v;\n"
                       "  A a;\n"
                       "  initial begin\n"
                       "    v = 8'h5A;\n"
                       "    a = '{1, 2, 3};\n"
                       "    #1 $display(\"%0d %h %0d %0d\", $bits(v), v, "
                       "$size(a), a[2]);\n"
                       "  end\n"
                       "endmodule\n"
                       "module Top; ifc x [2] (); sub s(x); endmodule\n",
                       f),
            "8 5a 3 3\n");
}

TEST(InterfacePortTypedefSim, TypeTakenThroughAPortKeepsItsUnpackedDimensions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  typedef byte IA [3];\n"
                       "  typedef int IQ [$];\n"
                       "  typedef int ID [];\n"
                       "  typedef int IS [string];\n"
                       "endinterface\n"
                       "module one(ifc i);\n"
                       "  typedef i.IA A;\n"
                       "  typedef i.IQ Q;\n"
                       "  typedef i.ID D;\n"
                       "  typedef i.IS S;\n"
                       "  A a;\n"
                       "  Q q;\n"
                       "  D d;\n"
                       "  S s;\n"
                       "  initial begin\n"
                       "    a = '{4, 5, 6};\n"
                       "    q.push_back(7);\n"
                       "    q.push_back(9);\n"
                       "    d = new[4];\n"
                       "    s[\"k\"] = 11;\n"
                       "    #1 $display(\"%0d %0d %0d %0d %0d %0d\", $size(a), "
                       "a[0], q.size(), q[$], d.size(), s[\"k\"]);\n"
                       "  end\n"
                       "endmodule\n"
                       "module Top; ifc y (); one o(y); endmodule\n",
                       f),
            "3 4 2 9 4 11\n");
}

}  // namespace
