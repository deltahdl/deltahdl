#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(HierarchicalNameSimulation, ReadChildInstanceVariable) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] val;\n"
      "  initial val = 8'd42;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = c1.val;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(HierarchicalNameSimulation, WriteChildInstanceVariable) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] val;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  initial begin\n"
      "    c1.val = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "c1.val");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(HierarchicalNameSimulation, MultiLevelHierarchicalRead) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module leaf;\n"
      "  logic [7:0] data;\n"
      "  initial data = 8'd77;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = m1.l1.data;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

TEST(HierarchicalNameSimulation, RootPrefixedHierarchicalRead) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] sig;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    sig = 8'd33;\n"
      "    #1;\n"
      "    result = $root.top.sig;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 33u);
}

TEST(HierarchicalNameSimulation, HierarchicalNameInEventExpression) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic done;\n"
      "  initial begin\n"
      "    done = 0;\n"
      "    #10 done = 1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd0;\n"
      "    @(posedge c1.done);\n"
      "    result = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

TEST(HierarchicalNames, InstanceArrayElementIsReachedByItsIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf #(parameter K = 0)();\n"
                       "  int v = K * 10 + 1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  leaf #(1) arr[2]();\n"
                       "  leaf #(5) one();\n"
                       "  initial begin\n"
                       "    arr[1].v = 11;\n"
                       "    #1 $display(\"%0d %0d %0d\", arr[1].v, arr[0].v, "
                       "one.v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "11 11 51\n");
}

TEST(HierarchicalNames, RangedInstanceArrayElementIsReachedByItsIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf(input i, output o);\n"
                       "  assign o = ~i;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  reg [1:0] a = 2'b01; wire [1:0] y;\n"
                       "  leaf arr[1:0](.i(a), .o(y));\n"
                       "  initial #1 $display(\"%b %b %b\", y, arr[1].o, "
                       "arr[0].o);\n"
                       "endmodule\n",
                       f),
            "10 1 0\n");
}

TEST(HierarchicalNames, ReadOfAnUnsignedVariableByHierarchicalNameIsUnsigned) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface I; logic w; endinterface\n"
                 "module sub;\n"
                 "  logic u;\n"
                 "  logic signed [3:0] s;\n"
                 "  int i;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  I a();\n"
                 "  sub b();\n"
                 "  initial begin\n"
                 "    a.w = 1; b.u = 1; b.s = -3; b.i = -5;\n"
                 "    #1 $display(\"%0d %0d %0d %0d\", a.w, b.u, b.s, b.i);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 1 -3 -5\n");
}

TEST(HierarchicalNames, RootHeadedArrayElementIsTheTopsElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  logic arr [1:0] = '{1, 1};\n"
                       "  initial begin\n"
                       "    arr[1] = 0;\n"
                       "    $root.top.arr[0] = 0;\n"
                       "    #1 $display(\"%0d %0d %0d\", $root.top.arr[1],\n"
                       "                $root.top.arr[0], arr[0]);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic arr [1:0] = '{1, 1};\n"
                       "  sub c();\n"
                       "endmodule\n",
                       f),
            "1 0 1\n");
}

TEST(HierarchicalNames, MemberOfAnotherInstancesStructureIsWritten) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int A; int B; } s_t;\n"
                       "module sub ();\n"
                       "  s_t v = '{A: 1, B: 2};\n"
                       "  initial #2 $display(\"A=%0d B=%0d\", v.A, v.B);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  sub s1 ();\n"
                       "  initial begin\n"
                       "    #1 s1.v.B = 9;\n"
                       "    s1.v.A <= 4;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "A=4 B=9\n");
}

TEST(HierarchicalNames, MemberOfATypeParameterStructureIsWritten) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int A; } a_t;\n"
                       "module ma #(parameter type t_3 = int) ();\n"
                       "  t_3 v3;\n"
                       "  initial #2 $display(\"A=%0d\", v3.A);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  ma #(.t_3(a_t)) s2 ();\n"
                       "  initial #1 s2.v3.A = 9;\n"
                       "endmodule\n",
                       f),
            "A=9\n");
}

TEST(HierarchicalNames, NameThroughAGenerateBlockReachesAnInstancesVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "module m2;\n"
      "  int n = 3;\n"
      "  int dbl;\n"
      "  always @(n) dbl = n * 2;\n"
      "endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    m2 c();\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : h\n"
      "    m2 d();\n"
      "  end\n"
      "  initial begin\n"
      "    #1 h[1].d.n = 7;\n"
      "    #1 $display(\"%0d %0d %0d %0d\", g.c.n, h[0].d.n, h[1].d.n,\n"
      "                h[1].d.dbl);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 3 7 14\n");
}

TEST(HierarchicalNameTree, OneNamedBlockInTwoInstancesIsTwoObjects) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mod(input in);\n"
                       "  always @(posedge in) begin : keep\n"
                       "    logic hold;\n    hold = in;\n  end\n"
                       "endmodule\n"
                       "module cct(input s1, s2);\n"
                       "  mod amod(s1), bmod(s2);\nendmodule\n"
                       "module wave;\n  logic s1 = 0, s2 = 0;\n"
                       "  cct a(s1, s2);\n"
                       "  initial begin\n    #1 s1 = 1;\n"
                       "    #1 $display(\"%b %b\", a.amod.keep.hold, "
                       "a.bmod.keep.hold);\n  end\nendmodule\n",
                       f),
            "1 x\n");
}

std::string OutputActualRun(const std::string& routine, SimFixture& f) {
  return RunCapture(
      "module leaf;\n  logic [3:0] v;\nendmodule\n"
      "module t;\n  leaf u();\n" +
          routine +
          "  initial begin\n    put(u.v);\n"
          "    #1 $display(\"%0d\", u.v);\n  end\nendmodule\n",
      f);
}

TEST(HierarchicalNameTree, AHierarchicalNameIsATasksOutputActual) {
  SimFixture f;
  EXPECT_EQ(OutputActualRun("  task put(output logic [3:0] o);\n"
                            "    o = 4'd9;\n  endtask\n",
                            f),
            "9\n");
}

TEST(HierarchicalNameTree, AHierarchicalNameIsAFunctionsOutputActual) {
  SimFixture f;
  EXPECT_EQ(OutputActualRun("  function void put(output logic [3:0] o);\n"
                            "    o = 4'd9;\n  endfunction\n",
                            f),
            "9\n");
}

TEST(HierarchicalNameTree, AnEscapedInstanceNameHeadsAPath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n  int v = 7;\nendmodule\n"
                       "module t;\n  leaf \\in-st ();\n"
                       "  initial #1 $display(\"%0d\", \\in-st .v);\n"
                       "endmodule\n",
                       f),
            "7\n");
}

TEST(HierarchicalNameTree, AnEscapedNameEndsAPath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n  int \\v-1  = 8;\nendmodule\n"
                       "module t;\n  leaf u();\n"
                       "  initial #1 $display(\"%0d\", u.\\v-1 );\n"
                       "endmodule\n",
                       f),
            "8\n");
}

TEST(HierarchicalNameTree, StaticLocalsAreReachedThroughTheirSubroutine) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n"
                       "  task tk;\n    static int n = 0;\n    n++;\n"
                       "  endtask\n"
                       "  function int fn;\n    static int k = 0;\n"
                       "    k++;\n    return k;\n  endfunction\n"
                       "endmodule\n"
                       "module t;\n  leaf u();\n  int r;\n"
                       "  initial begin\n    u.tk();\n    u.tk();\n"
                       "    r = u.fn();\n"
                       "    #1 $display(\"%0d %0d\", u.tk.n, u.fn.k);\n"
                       "  end\nendmodule\n",
                       f),
            "2 1\n");
}

TEST(HierarchicalNameTree, ALaterForkWritesAnEarlierForksVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  initial begin\n"
                       "    fork : mod_1\n      reg x;\n"
                       "      #2 $display(\"%b\", x);\n    join_none\n"
                       "    fork : mod_2\n      reg x;\n"
                       "      #1 mod_1.x = 1;\n    join_none\n"
                       "  end\nendmodule\n",
                       f),
            "1\n");
}

TEST(HierarchicalNameTree, AnElementOfATwoDimensionalInstanceArray) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n  int v;\nendmodule\n"
                       "module t;\n  leaf u [0:3][0:3] ();\n"
                       "  initial begin\n    u[1][2].v = 6;\n"
                       "    #1 $display(\"%0d %0d\", u[1][2].v, u[2][1].v);\n"
                       "  end\nendmodule\n",
                       f),
            "6 0\n");
}

TEST(HierarchicalNameTree, APathMayEndAtAnArrayOrLoopBlockName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\nendmodule\n"
                       "module t;\n  leaf u [0:3] ();\n"
                       "  for (genvar i = 0; i < 4; i++) begin : blk\n"
                       "    int w = i;\n  end\n"
                       "  initial begin\n    $printtimescale(u);\n"
                       "    $printtimescale(t.blk);\n  end\nendmodule\n",
                       f),
            "Time scale of (u) is 1ns / 1ns\n"
            "Time scale of (t.blk) is 1ns / 1ns\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
