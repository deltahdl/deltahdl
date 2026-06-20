
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     UnpackedArrayPortMatchingDimensionsAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input [7:0] data [4]);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] arr [4];\n"
             "  child u(.data(arr));\n"
             "endmodule\n"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     UnpackedArrayPortDimensionCountMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input [7:0] data [4]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] arr [2][2];\n"
      "  child u(.data(arr));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     UnpackedArrayPortDimensionSizeMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input [7:0] data [4]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] arr [3];\n"
      "  child u(.data(arr));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     UnpackedArrayPortScalarConnectedToArrayPortErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input [7:0] data [4]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] scalar;\n"
      "  child u(.data(scalar));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     ScalarConnectionReplicatedToArrayOfInstances) {
  EXPECT_TRUE(
      ElabOk("module child(input [7:0] i, output o);\n"
             "  assign o = i[0];\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  logic [3:0] y;\n"
             "  child c[3:0](.i(x), .o(y));\n"
             "endmodule\n"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     ScalarConnectionToSingleInstanceAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input [7:0] i, output o);\n"
             "  assign o = i[0];\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  logic y;\n"
             "  child c(.i(x), .o(y));\n"
             "endmodule\n"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     UnpackedArrayConnectionMatchingInstanceArrayAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input [7:0] i, output o);\n"
             "  assign o = i[0];\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] arr [4];\n"
             "  logic [3:0] out;\n"
             "  child c[3:0](.i(arr), .o(out));\n"
             "endmodule\n"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     UnpackedArrayConnectionDimensionMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input [7:0] i, output o);\n"
      "  assign o = i[0];\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] arr [3];\n"
      "  logic [3:0] out;\n"
      "  child c[3:0](.i(arr), .o(out));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     MultiDimensionalInstanceArrayWithMatchingUnpackedArrayAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(output o, input i[5]);\n"
             "endmodule\n"
             "module top;\n"
             "  logic o [8][4];\n"
             "  logic i [8][4][5];\n"
             "  child c[8][4](.o(o), .i(i));\n"
             "endmodule\n"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     MultiDimensionalInstanceArrayPortDimensionSizeMismatchErrors) {
  // The instance-array dimensions match ([8][4]), but the trailing dimension
  // that must line up with the per-instance unpacked port (declared as [5])
  // is connected with size 3, so the port-dimension comparison must fail.
  ElabFixture f;
  ElaborateSrc(
      "module child(output o, input i[5]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic o [8][4];\n"
      "  logic i [8][4][3];\n"
      "  child c[8][4](.o(o), .i(i));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     PackedArrayConnectionMatchingBitCountAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input [7:0] i, output o);\n"
             "  assign o = i[0];\n"
             "endmodule\n"
             "module top;\n"
             "  logic [31:0] bus;\n"
             "  logic [3:0] out;\n"
             "  child c[3:0](.i(bus), .o(out));\n"
             "endmodule\n"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     PackedArrayConnectionTooManyBitsErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input [7:0] i, output o);\n"
      "  assign o = i[0];\n"
      "endmodule\n"
      "module top;\n"
      "  logic [39:0] bus;\n"
      "  logic [3:0] out;\n"
      "  child c[3:0](.i(bus), .o(out));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     PackedArrayConnectionTooFewBitsErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input [7:0] i, output o);\n"
      "  assign o = i[0];\n"
      "endmodule\n"
      "module top;\n"
      "  logic [23:0] bus;\n"
      "  logic [3:0] out;\n"
      "  child c[3:0](.i(bus), .o(out));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     SingleElementInstanceArrayAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input [7:0] i, output o);\n"
             "  assign o = i[0];\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  logic y;\n"
             "  child c[0:0](.i(x), .o(y));\n"
             "endmodule\n"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     InstanceArrayWithPositionalPortsAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input [7:0] i, output o);\n"
             "  assign o = i[0];\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] x;\n"
             "  logic [3:0] y;\n"
             "  child c[3:0](x, y);\n"
             "endmodule\n"));
}

}  // namespace
