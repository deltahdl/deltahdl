#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(InterfaceInstanceArraySim, ElementsHoldMembersAndParameters) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface myif #(parameter P = 7); int x; "
                       "endinterface\n"
                       "module top;\n"
                       "  myif #(100) scalar1(), vector[3:0]();\n"
                       "  myif plain();\n"
                       "  myif pv[1:0]();\n"
                       "  initial begin\n"
                       "    vector[2].x = 12;\n"
                       "    plain.x = 3;\n"
                       "    pv[0].x = 5;\n"
                       "    $display(\"P=%0d P=%0d P=%0d x=%0d x=%0d x=%0d\", "
                       "vector[3].P, plain.P, pv[1].P, vector[2].x, plain.x, "
                       "pv[0].x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "P=100 P=7 P=7 x=12 x=3 x=5\n");
}

TEST(InterfacePortHierRefSim, PortJoinsAnInstanceAnotherModuleDeclares) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [7:0] a = 1; endinterface\n"
                       "module holder; ifc i(); endmodule\n"
                       "module writer(ifc p); initial p.a = 9; endmodule\n"
                       "module reader(ifc p);\n"
                       "  initial #1 $display(\"x=%0d\", p.a);\n"
                       "endmodule\n"
                       "module top; writer w(h.i); holder h(); reader r(h.i);\n"
                       "endmodule\n",
                       f),
            "x=9\n");
}

TEST(InterfacePortHierRefSim, PortJoinsTheInstanceNamedFromTheModule) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [7:0] a = 1; endinterface\n"
                       "module writer(ifc p); initial p.a = 9; endmodule\n"
                       "module top; ifc i(); writer w(top.i);\n"
                       "  initial #1 $display(\"x=%0d\", i.a);\n"
                       "endmodule\n",
                       f),
            "x=9\n");
}

TEST(InterfacePortHierRefSim, PortJoinsTheInstanceNamedFromTheTop) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [7:0] a = 1; endinterface\n"
                       "module writer(ifc p); initial p.a = 9; endmodule\n"
                       "module mid; writer w(top.i); endmodule\n"
                       "module top; ifc i(); mid m();\n"
                       "  initial #1 $display(\"x=%0d\", i.a);\n"
                       "endmodule\n",
                       f),
            "x=9\n");
}

TEST(InterfacePortHierRefSim, PortJoinsAnInstanceTheTopDeclaresLater) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [7:0] a = 1; endinterface\n"
                       "module writer(ifc p); initial p.a = 9; endmodule\n"
                       "module mid; writer w(top.i); endmodule\n"
                       "module top; mid m(); ifc i();\n"
                       "  initial #1 $display(\"x=%0d\", i.a);\n"
                       "endmodule\n",
                       f),
            "x=9\n");
}

TEST(InterfacePortHierRefSim, PortJoinsAnInstanceOfALaterTop) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "interface ifc; logic [7:0] a = 1; endinterface\n"
      "module writer(ifc p); initial p.a = 9; endmodule\n"
      "module mid; writer w(t2.i); endmodule\n"
      "module t1; mid m(); endmodule\n"
      "module t2; ifc i(); endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"t2.i.a", 9u}});
}

TEST(InterfacePortIntoGenerateBlockSim,
     PortReachesTheInterfaceThroughTheBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [7:0] a = 1; endinterface\n"
                       "module leaf(ifc p); initial p.a = 9; endmodule\n"
                       "module mid(ifc p); leaf l(p); endmodule\n"
                       "module outer(ifc p); if (1) begin : gb mid m(p); end\n"
                       "endmodule\n"
                       "module top; ifc i(); outer o(i);\n"
                       "  initial #1 $display(\"x=%0d\", i.a);\n"
                       "endmodule\n",
                       f),
            "x=9\n");
}

}  // namespace
