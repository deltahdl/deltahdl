#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SpecifyPathSim, SimpleParallelPathSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(SpecifyPathSim, BitSelectDriverOfAPathOutputTakesThePathDelay) {
  SimFixture f;
  std::string out = RunCapture(
      "module top(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] sa;\n"
      "  assign a = sa;\n"
      "  assign y[1] = a[1];\n"
      "  specify\n"
      "    (a => y) = 6;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    sa = 8'h00;\n"
      "    #20 sa = 8'h02;\n"
      "  end\n"
      "  initial #24 $display(\"s24=%b\", y[1]);\n"
      "  initial #28 $display(\"s28=%b\", y[1]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s24=0\ns28=1\n");
}

TEST(SpecifyPathSim, PartSelectDriverOfAPathOutputTakesThePathDelay) {
  SimFixture f;
  std::string out = RunCapture(
      "module top(input [7:0] a, output [7:0] y);\n"
      "  logic [7:0] sa;\n"
      "  assign a = sa;\n"
      "  assign y[5:4] = a[5:4];\n"
      "  specify\n"
      "    (a => y) = 6;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    sa = 8'h00;\n"
      "    #20 sa = 8'h10;\n"
      "  end\n"
      "  initial #24 $display(\"s24=%b\", y[4]);\n"
      "  initial #28 $display(\"s28=%b\", y[4]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s24=0\ns28=1\n");
}

TEST(SpecifyPathSim, SelectDriverOfANonPathNetTakesNoPathDelay) {
  SimFixture f;
  std::string out = RunCapture(
      "module top(input [7:0] a, output [7:0] y, output [7:0] z);\n"
      "  logic [7:0] sa;\n"
      "  assign a = sa;\n"
      "  assign y[1] = a[1];\n"
      "  assign z[1] = a[1];\n"
      "  specify\n"
      "    (a => y) = 6;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    sa = 8'h00;\n"
      "    #20 sa = 8'h02;\n"
      "  end\n"
      "  initial #22 $display(\"y=%b z=%b\", y[1], z[1]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=0 z=1\n");
}

TEST(SpecifyPathSim, InterfacePortSignalIsAPathSource) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc;\n"
      "  logic a;\n"
      "endinterface\n"
      "module mybuf(ifc p, output y);\n"
      "  assign y = p.a;\n"
      "  specify\n"
      "    (p.a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  ifc i();\n"
      "  wire ty;\n"
      "  mybuf u(.p(i), .y(ty));\n"
      "  always @(ty) if ($time >= 8) $display(\"t=%0t y=%b\", $time, ty);\n"
      "  initial begin\n"
      "    i.a = 0;\n"
      "    #10 i.a = 1;\n"
      "    #10 i.a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=15 y=1\n"
            "t=25 y=0\n");
}

TEST(SpecifyPathSim, AssignReadingAnInterfacePortFollowsIt) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc;\n"
      "  logic a;\n"
      "endinterface\n"
      "module mybuf(ifc p, output y);\n"
      "  assign y = p.a;\n"
      "endmodule\n"
      "module top;\n"
      "  ifc i();\n"
      "  wire ty;\n"
      "  mybuf u(.p(i), .y(ty));\n"
      "  always @(ty) if ($time >= 8) $display(\"t=%0t y=%b\", $time, ty);\n"
      "  initial begin\n"
      "    i.a = 0;\n"
      "    #10 i.a = 1;\n"
      "    #10 i.a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=10 y=1\n"
            "t=20 y=0\n");
}

TEST(SimpleModulePathRun, BitSelectTerminalsDeclareOnePathPerBit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mybus(input [1:0] a, output [1:0] y);\n"
                       "  assign y = a;\n"
                       "  specify\n"
                       "    (a[0] => y[0]) = 2;\n"
                       "    (a[1] => y[1]) = 5;\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic [1:0] a;\n"
                       "  wire [1:0] ty;\n"
                       "  mybus u(.a(a), .y(ty));\n"
                       "  always @(ty) if ($time >= 8)\n"
                       "    $display(\"t=%0t y=%b\", $time, ty);\n"
                       "  initial begin\n"
                       "    a = 2'b00;\n"
                       "    #10 a[0] = 1;\n"
                       "    #10 a[1] = 1;\n"
                       "    #10 a[0] = 0;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=12 y=01\nt=25 y=11\nt=32 y=10\n");
}

}  // namespace
