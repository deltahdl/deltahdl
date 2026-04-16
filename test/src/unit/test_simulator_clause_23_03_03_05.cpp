
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- R2: If the size and type of the port connection match a single instance
//     port, the connection shall be made to each instance in an array of
//     instances ---

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

// --- R3: Unpacked array connection maps elements to instances ---

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

// --- R4: Packed array connection part-selects bits across instances ---

TEST(UnpackedArrayPortsAndArraysOfInstancesSimulation,
     PackedArrayConnectionPartSelectsAcrossInstances) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input [7:0] i, output [7:0] o);\n"
      "  assign o = i;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [15:0] bus = 16'hCAFE;\n"
      "  logic [15:0] result;\n"
      "  child c[1:0](.i(bus), .o(result));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

}  // namespace
