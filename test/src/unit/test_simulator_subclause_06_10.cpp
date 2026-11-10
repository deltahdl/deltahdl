#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ImplicitNetSimulation, InterfaceProgramAndStaticCheckerPortsDeclareNets) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface i(input logic a);\n"
                       "endinterface\n"
                       "program p(input logic a);\n"
                       "endprogram\n"
                       "checker c(logic a);\n"
                       "endchecker\n"
                       "module t;\n"
                       "  i ii(n1);\n"
                       "  p pp(n2);\n"
                       "  c cc(n3);\n"
                       "  assign n1 = 1;\n"
                       "  assign n2 = 0;\n"
                       "  initial #1 $display(\"%b %b %b %0d %0d %0d\", n1, "
                       "n2, n3, $bits(n1),\n"
                       "                      $bits(n2), $bits(n3));\n"
                       "endmodule\n",
                       f),
            "1 0 z 1 1 1\n");
}

TEST(ImplicitNetSimulation, InstancePortsInsideAnInterfaceAndAGenerateBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface i(input logic a);\n"
                       "endinterface\n"
                       "interface j;\n"
                       "  i ii(nj);\n"
                       "  assign nj = 1;\n"
                       "endinterface\n"
                       "module t;\n"
                       "  j jj();\n"
                       "  if (1) begin : g\n"
                       "    i ii(ng);\n"
                       "    assign ng = 0;\n"
                       "  end\n"
                       "  initial #1 $display(\"%b %b\", jj.nj, g.ng);\n"
                       "endmodule\n",
                       f),
            "1 0\n");
}

TEST(ImplicitNetSimulation, CompilationUnitNamesAreNoImplicitNets) {
  SimFixture f;
  EXPECT_EQ(RunCapture("wire n;\n"
                       "logic v = 1;\n"
                       "module s(input logic a);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  s u(v);\n"
                       "  assign n = 1;\n"
                       "  initial #1 $display(\"%b %b\", $unit::n, u.a);\n"
                       "endmodule\n",
                       f),
            "1 1\n");
}

TEST(ImplicitNetSimulation, DISABLED_ImportedNamesAreNoImplicitNets) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package k;\n"
                       "  logic x = 1;\n"
                       "  logic y = 1;\n"
                       "  logic p;\n"
                       "  logic q;\n"
                       "endpackage\n"
                       "module s(input logic a);\n"
                       "endmodule\n"
                       "module e;\n"
                       "  import k::x;\n"
                       "  import k::p;\n"
                       "  s u(x);\n"
                       "  assign p = 0;\n"
                       "endmodule\n"
                       "module w;\n"
                       "  import k::*;\n"
                       "  s u(y);\n"
                       "  assign q = 0;\n"
                       "endmodule\n"
                       "module t;\n"
                       "  e ee();\n"
                       "  w ww();\n"
                       "  initial #1 $display(\"%b %b %b %b\", ee.u.a, ww.u.a, "
                       "k::p, k::q);\n"
                       "endmodule\n",
                       f),
            "1 1 0 0\n");
}

}  // namespace
