
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

// §23.3.3.5 (printed page 748): an unpacked array connection is split across
// an array of instances, each element of the connection matched to the port
// left index to left index and right index to right index: u[3], the leftmost
// of u[3:0], takes ins[0], the leftmost of ins[0:3], and its output lands in
// outs[0]. The element was chosen counting from the right end of the instance
// array and the left end of the connection, so u[3] took ins[3]. `leaf k[3]` is
// k[0] to k[2], three instances, each on its own element; it was one instance,
// k[1] and k[2] never driven.
TEST(UnpackedArrayPortsAndArraysOfInstancesSimulation,
     UnpackedConnectionMatchesLeftIndexToLeftIndex) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module leaf(input logic a, output logic y);\n"
                 "  assign y = ~a;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  logic ins[0:3] = '{1'b1, 1'b1, 1'b0, 1'b0};\n"
                 "  logic outs[0:3];\n"
                 "  logic tri3[3] = '{1'b0, 1'b1, 1'b1};\n"
                 "  logic y3[3];\n"
                 "  leaf u[3:0](.a(ins), .y(outs));\n"
                 "  leaf k[3](.a(tri3), .y(y3));\n"
                 "  initial #1 $display(\"%b%b%b%b %b%b%b%b %b%b%b %b%b%b\",\n"
                 "      u[3].a, u[2].a, u[1].a, u[0].a,\n"
                 "      outs[0], outs[1], outs[2], outs[3],\n"
                 "      k[0].a, k[1].a, k[2].a, y3[0], y3[1], y3[2]);\n"
                 "endmodule\n",
                 f),
      "1100 0011 011 100\n");
}

// §23.3.3.5 (printed page 748): an unpacked array port connected to an
// unpacked array has each element of the connection matched to the port left
// index to left index, so `input var int i[3]` on `int one[3] = '{5, 6, 7}`
// reads 5, 6 and 7, and `input logic [3:0] l[2]` on `'{9, 10}` reads 9 and 10
// -- unsigned, as the element is declared. The port was one value of an
// element's width, i[0] to i[2] reading the bits of 7 and l[0], l[1] those of
// 10; s.i[1] names the port's element from above.
TEST(UnpackedArrayPortsAndArraysOfInstancesSimulation,
     UnpackedArrayPortReadsEachElementOfItsConnection) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(input var int i[3], input logic [3:0] "
                       "l[2]);\n"
                       "  initial #1 $display(\"child i %0d %0d %0d l %0d "
                       "%0d\", i[0], i[1], i[2], l[0], l[1]);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  int one[3] = '{5, 6, 7};\n"
                       "  logic [3:0] lv[2] = '{9, 10};\n"
                       "  child s(one, lv);\n"
                       "  initial #2 $display(\"s.i %0d\", s.i[1]);\n"
                       "endmodule\n",
                       f),
            "child i 5 6 7 l 9 10\ns.i 6\n");
}

// An output array port drives its connection element by element, left to
// left across ranges that run opposite ways: o[0] of `int o[0:2]` lands in
// res[3] of `int res[3:1]`. The input d[2:0] on dv[0:2] reads d[2] from
// dv[0]. An array of instances over a two-dimensional array hands each
// instance one row for its array port (`child c[3](oo, arr)`), and each
// instance's output drives one element of the net array oo.
TEST(UnpackedArrayPortsAndArraysOfInstancesSimulation,
     UnpackedArrayPortsConnectLeftIndexToLeftIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module src(output int o[0:2], input logic [7:0] "
                       "d[2:0]);\n"
                       "  assign o[0] = 10;\n"
                       "  assign o[1] = 20;\n"
                       "  assign o[2] = d[2] + d[0];\n"
                       "endmodule\n"
                       "module child(output logic o, input var int i[3]);\n"
                       "  assign o = (i[0] + i[1] + i[2]) > 10;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  int res[3:1];\n"
                       "  logic [7:0] dv[0:2] = '{1, 2, 3};\n"
                       "  int arr[3][3];\n"
                       "  wire oo[3];\n"
                       "  src u(.o(res), .d(dv));\n"
                       "  child c[3](oo, arr);\n"
                       "  initial begin\n"
                       "    arr = '{'{4, 5, 6}, '{1, 2, 3}, '{9, 9, 1}};\n"
                       "    #1 $display(\"%0d %0d %0d o %b%b%b\", res[3], "
                       "res[2], res[1], oo[0], oo[1], oo[2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "10 20 4 o 101\n");
}

// §23.3.3.3 makes an inout port one net with its connection, and an array
// port is so element by element: the parent drives bus[0] and the child b[1],
// and each is seen from both sides. §7.4.2 (printed page 154) has "Net arrays
// are useful for connecting to ports of module instances", and the net array
// was refused as a connection at all, the check asking for a variable array.
TEST(UnpackedArrayPortsAndArraysOfInstancesSimulation,
     InoutArrayPortIsItsNetArrayElementByElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module io(inout wire [3:0] b[2]);\n"
                       "  assign b[1] = 4'h7;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire [3:0] bus[2];\n"
                       "  assign bus[0] = 4'h3;\n"
                       "  io u(bus);\n"
                       "  initial #1 $display(\"%h %h %h %h\", bus[0], bus[1], "
                       "u.b[0], u.b[1]);\n"
                       "endmodule\n",
                       f),
            "3 7 3 7\n");
}

// §10.7 gives an element the value of its declared type, and §6.11.3 its
// signedness by the declaration: `logic [3:0] d [2]` written 4'sd9, by a
// statement or a continuous assignment, reads 9, as a scalar of that type
// does, while `int c [2]` in a block keeps -9. The element reads took the
// signedness of the last value stored, so the first read -7, and the block's
// elements were created with none, so the second read 4294967287.
TEST(UnpackedArraySimulation, ElementsReadWithTheirDeclaredSignedness) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [3:0] a[2], d[2];\n"
                       "  assign a[0] = 4'sd9;\n"
                       "  initial begin\n"
                       "    automatic int c[2];\n"
                       "    d[0] = 4'sd9;\n"
                       "    c[1] = -9;\n"
                       "    #1 $display(\"%0d %0d %0d\", a[0], d[0], c[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "9 9 -9\n");
}

}  // namespace
