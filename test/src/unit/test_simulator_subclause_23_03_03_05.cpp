
#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(UnpackedArrayPortsAndArraysOfInstancesSimulation,
     ScalarConnectionReplicatedToAllInstances) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input [7:0] i, output [7:0] o);\n"
      "  assign o = i;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x = 8'hAB;\n"
      "  logic [7:0] y0, y1;\n"
      "  child c[1:0](.i(x), .o({y1, y0}));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v0 = f.ctx.FindVariable("y0");
  auto* v1 = f.ctx.FindVariable("y1");
  ASSERT_NE(v0, nullptr);
  ASSERT_NE(v1, nullptr);
  EXPECT_EQ(v0->value.ToUint64(), 0xABu);
  EXPECT_EQ(v1->value.ToUint64(), 0xABu);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesSimulation,
     UnpackedArrayConnectionMapsElementsToInstances) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input [7:0] i, output [7:0] o);\n"
      "  assign o = i + 1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] arr [2];\n"
      "  logic [7:0] out [2];\n"
      "  initial begin\n"
      "    arr[0] = 8'h10;\n"
      "    arr[1] = 8'h20;\n"
      "  end\n"
      "  child c[1:0](.i(arr), .o(out));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* v0 = f.ctx.FindVariable("out[0]");
  auto* v1 = f.ctx.FindVariable("out[1]");
  ASSERT_NE(v0, nullptr);
  ASSERT_NE(v1, nullptr);
  EXPECT_EQ(v0->value.ToUint64(), 0x11u);
  EXPECT_EQ(v1->value.ToUint64(), 0x21u);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesSimulation,
     PackedArrayConnectionPartSelectsAcrossInstances) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input [7:0] i, output [7:0] o);\n"
      "  assign o = i;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [15:0] bus = 16'hCAFE;\n"
      "  logic [15:0] result;\n"
      "  child c[1:0](.i(bus), .o(result));\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

// §23.3.3.5 (printed page 748): a packed port connection wider than one
// instance's port gives each instance of the array a part-select, the
// rightmost instance the rightmost bits, so four `xcell`s -- each an `xor`
// on scalar ports, §28.3.6 (printed page 833) -- on `4'b1100` and `4'b1010`
// drive `0110` onto the parent's four-bit net. The net output port of each
// instance left y all x.
TEST(UnpackedArrayPortsAndArraysOfInstancesSimulation,
     InstanceArrayGivesEachInstanceItsBitsOfAVectorNet) {
  SimFixture f;
  auto out = RunCapture(
      "module xcell (output y, input a, b);\n"
      "  xor g (y, a, b);\n"
      "endmodule\n"
      "module top;\n"
      "  wire [3:0] y;\n"
      "  logic [3:0] a = 4'b1100, b = 4'b1010;\n"
      "  xcell c[3:0] (y, a, b);\n"
      "  initial #1 $display(\"y=%b\", y);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "y=0110\n");
}

}  // namespace
