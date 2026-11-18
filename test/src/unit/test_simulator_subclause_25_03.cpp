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

TEST(InterfaceInModuleSim, AnInterfaceDeclaredAndInstantiatedInAModuleRuns) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  interface ifc;\n"
                       "    logic [7:0] a = 5;\n"
                       "    wire [7:0] twice;\n"
                       "    assign twice = a * 8'd2;\n"
                       "  endinterface\n"
                       "  ifc i();\n"
                       "  initial begin\n"
                       "    #1 $display(\"a=%0d twice=%0d\", i.a, i.twice);\n"
                       "    i.a = 8'd7;\n"
                       "    #1 $display(\"a=%0d twice=%0d\", i.a, i.twice);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "a=5 twice=10\na=7 twice=14\n");
}

TEST(InterfaceInModuleSim, AnInterfaceDeclaredInAModuleIsNeverImplicitlyRun) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  interface ifc;\n"
                       "    initial $display(\"ifc ran\");\n"
                       "  endinterface\n"
                       "  module sub;\n"
                       "    initial $display(\"sub ran\");\n"
                       "  endmodule\n"
                       "endmodule\n",
                       f),
            "sub ran\n");
}

TEST(InterfaceBodySim, EachInstancesAlwaysCombFollowsItsOwnInput) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic a, b; always_comb b = a;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  ifc i1(), i2();\n"
                       "  initial begin\n"
                       "    #1 i1.a = 1; i2.a = 0;\n"
                       "    #1 $display(\"%b %b\", i1.b, i2.b);\n"
                       "    i1.a = 0; i2.a = 1;\n"
                       "    #1 $display(\"%b %b\", i1.b, i2.b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 0\n0 1\n");
}

TEST(InterfaceBodySim, EachInstancesAlwaysFfSamplesAtItsOwnClockEdge) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic clk = 0, d, q;\n"
                       "  always_ff @(posedge clk) q <= d;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  ifc i1(), i2();\n"
                       "  initial begin\n"
                       "    i1.d = 1; i2.d = 0;\n"
                       "    #1 i1.clk = 1;\n"
                       "    #1 $display(\"%b %b\", i1.q, i2.q);\n"
                       "    i1.d = 0; i1.clk = 0;\n"
                       "    #1 $display(\"%b %b\", i1.q, i2.q);\n"
                       "    i2.d = 1; i2.clk = 1;\n"
                       "    #1 $display(\"%b %b\", i1.q, i2.q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 x\n1 x\n1 1\n");
}

TEST(InterfaceBodySim, EachInstancesAlwaysLatchFollowsWhileEnabled) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic en = 0, d, q;\n"
                       "  always_latch if (en) q <= d;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  ifc i1(), i2();\n"
                       "  initial begin\n"
                       "    #1 i1.en = 1; i1.d = 1; i2.d = 1;\n"
                       "    #1 $display(\"%b %b\", i1.q, i2.q);\n"
                       "    i1.d = 0;\n"
                       "    #1 $display(\"%b %b\", i1.q, i2.q);\n"
                       "    i1.en = 0;\n"
                       "    #1 i1.d = 1;\n"
                       "    #1 $display(\"%b %b\", i1.q, i2.q);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 x\n0 x\n0 x\n");
}

TEST(InterfaceBodySim, EachInstancesContinuousAssignToAVariableFollows) {
  SimFixture f;
  auto out = RunCapture(
      "interface ifc; logic a, v; assign v = a; endinterface\n"
      "module top;\n"
      "  ifc i1(), i2();\n"
      "  initial begin\n"
      "    #1 i1.a = 1; i2.a = 0;\n"
      "    #1 $display(\"%b %b\", i1.v, i2.v);\n"
      "    i1.a = 0; i2.a = 1;\n"
      "    #1 $display(\"%b %b\", i1.v, i2.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "1 0\n0 1\n");
}

TEST(InterfaceBodySim, EachInstancesCoverStatementCountsItsOwnMatches) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface ifc; logic clk = 0, req = 0, gnt = 0; int n = 0;\n"
                 "  cover property (@(posedge clk) req ##1 gnt) n++;\n"
                 "endinterface\n"
                 "module top;\n"
                 "  ifc a(), b();\n"
                 "  always #5 begin a.clk = ~a.clk; b.clk = ~b.clk; end\n"
                 "  initial begin\n"
                 "    a.req = 1; b.req = 1;\n"
                 "    #10 a.req = 0; b.req = 0; a.gnt = 1; b.gnt = 1;\n"
                 "    #10 a.req = 1; b.req = 1; a.gnt = 0; b.gnt = 0;\n"
                 "    #10 a.req = 0; b.req = 0; a.gnt = 1;\n"
                 "    #10 a.gnt = 0;\n"
                 "    #20 $display(\"%0d %0d\", a.n, b.n);\n"
                 "    $finish;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "2 1\n$finish at time 60\n");
}

TEST(InterfaceBodySim, EachInstancesImmediateAssertionChecksItsOwnEdges) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic clk = 0, req = 0, gnt = 0;\n"
                       "  always @(posedge clk) assert (req || !gnt)\n"
                       "    else $display(\"%m grant at %0t\", $time);\n"
                       "endinterface\n"
                       "module top;\n"
                       "  ifc a(), b();\n"
                       "  initial begin\n"
                       "    a.gnt = 1; b.gnt = 1; b.req = 1;\n"
                       "    #1 a.clk = 1; b.clk = 1;\n"
                       "    #1 a.clk = 0; b.clk = 0; a.req = 1; b.req = 0;\n"
                       "    #1 a.clk = 1; b.clk = 1;\n"
                       "    #1 a.clk = 0; b.clk = 0; a.gnt = 0; b.gnt = 0;\n"
                       "    #1 a.clk = 1; b.clk = 1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "top.a grant at 1\ntop.b grant at 3\n");
}

}  // namespace
