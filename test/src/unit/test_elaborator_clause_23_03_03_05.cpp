
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- R1: For an unpacked array port, the port and the array connected to the
//     port shall have the same number of unpacked dimensions, and each
//     dimension shall have the same size as the corresponding dimension of the
//     array being connected ---

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

// --- R2: If the size and type of the port connection match a single instance
//     port, the connection shall be made to each instance in an array of
//     instances ---

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

// --- R3: If the port connection is an unpacked array, the slowest varying
//     dimensions shall be compared with the instance array dimensions. Matching
//     size maps element to element; mismatch is an error ---

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

// --- R4: If the port connection is a packed array, each instance gets a
//     part-select starting from the rightmost indices. Too many or too few bits
//     is an error ---

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

// --- Edge cases ---

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
