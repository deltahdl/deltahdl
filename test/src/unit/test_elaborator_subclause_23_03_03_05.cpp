#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array port 'data' has 1 unpacked "
                            "dimension(s) but connection has 2",
                            5, "23.3.3.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array port 'data' dimension 0 has size 4 "
                            "but connection has size 3",
                            5, "23.3.3.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array port 'data' requires a matching "
                            "unpacked array connection",
                            5, "23.3.3.5"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     MultiDimensionalUnpackedArrayPortMatchingDimensionsAccepted) {
  EXPECT_TRUE(
      ElabOk("module child(input [7:0] data [2][3]);\n"
             "endmodule\n"
             "module top;\n"
             "  logic [7:0] arr [2][3];\n"
             "  child u(.data(arr));\n"
             "endmodule\n"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     MultiDimensionalUnpackedArrayPortInnerDimensionSizeMismatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input [7:0] data [2][3]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] arr [2][4];\n"
      "  child u(.data(arr));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array port 'data' dimension 1 has size 3 "
                            "but connection has size 4",
                            5, "23.3.3.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array connection to port 'i' dimension 0 "
                            "has size 3 but instance array has size 4",
                            7, "23.3.3.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array connection to port 'i' port "
                            "dimension 0 has size 3 but port expects 5",
                            6, "23.3.3.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed array connection to port 'i' has width 40 "
                            "but expected 32 (4 instances * port width 8)",
                            7, "23.3.3.5"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "packed array connection to port 'i' has width 24 "
                            "but expected 32 (4 instances * port width 8)",
                            7, "23.3.3.5"));
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

TEST(InstanceArrayElaboration, AnElementRecordsItsArrayAndIndex) {
  ElabFixture f;
  auto* design = Elaborate(
      "module sub; endmodule\n"
      "module top; sub arr[2:4] (); sub one (); endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const auto& children = design->top_modules[0]->children;
  ASSERT_EQ(children.size(), 4U);
  for (const auto& child : children) {
    if (child.inst_name == "one") {
      EXPECT_TRUE(child.array.name.empty());
      continue;
    }
    EXPECT_EQ(child.array.name, "arr") << child.inst_name;
    EXPECT_EQ(child.array.left, 2);
    EXPECT_EQ(child.array.right, 4);
    EXPECT_EQ(child.inst_name,
              "arr[" + std::to_string(child.array.index) + "]");
  }
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     UntypedPatternConnectedToUnpackedArrayInputIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(input var int p [0:1]);\n"
      "endmodule\n"
      "module t;\n"
      "  sub s(.p('{5, 6}));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     ElementAndSliceConnectedToMatchingPortAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module sa(input logic [3:0] p [2]);\n"
      "endmodule\n"
      "module top;\n"
      "  localparam int L = 1;\n"
      "  logic [3:0] m [3][2];\n"
      "  logic [3:0] r [4];\n"
      "  sa u1(.p(m[1]));\n"
      "  sa u2(.p(r[1:2]));\n"
      "  sa u3(.p(r[L+:2]));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     ElementAndSliceOfTheWrongShapeAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "module sa(input logic [3:0] p [2]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] r [4];\n"
      "  sa u1(.p(r[0:2]));\n"
      "  sa u2(.p(r[1]));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array port 'p' dimension 0 has size 2 "
                            "but connection has size 3",
                            5, "23.3.3.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array port 'p' has 1 unpacked "
                            "dimension(s) but connection has 0",
                            6, "23.3.3.5"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     DescendingAndUnfoldedSlicesConnectToAMatchingPort) {
  ElabFixture f;
  ElaborateSrc(
      "module sa(input logic [3:0] p [2]);\n"
      "endmodule\n"
      "module top;\n"
      "  int i, j, w;\n"
      "  logic [3:0] r [4];\n"
      "  sa u1(.p(r[2-:2]));\n"
      "  sa u2(.p(r[i:j]));\n"
      "  sa u3(.p(r[1+:w]));\n"
      "  sa u4(.p(r[1:j]));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "dimension 0 has size", 6,
                             "23.3.3.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "dimension 0 has size", 7,
                             "23.3.3.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "dimension 0 has size", 8,
                             "23.3.3.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "dimension 0 has size", 9,
                             "23.3.3.5"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     SelectPastTheUnpackedDimensionsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module sa(input logic [3:0] p [2]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [3:0] r [4];\n"
      "  sa u1(.p(r[1][0]));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array port 'p' requires a matching "
                            "unpacked array connection",
                            5, "23.3.3.5"));
}

TEST(UnpackedArrayPortElaboration, InterfaceArrayOfAnotherSizeIsAnError) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; logic a; endinterface\n"
      "module user(ifc p[2]); endmodule\n"
      "module top;\n"
      "  ifc ia[1:3]();\n"
      "  user u(ia);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dimension 0 has size 2 but connection has size 3",
                            5, "23.3.3.5"));
}

TEST(UnpackedArrayPortElaboration, ScalarInterfaceOnAnInterfaceArrayPortFails) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; logic a; endinterface\n"
      "module user(ifc p[2]); endmodule\n"
      "module top;\n"
      "  ifc i();\n"
      "  user u(i);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "requires a matching unpacked array connection", 5,
                            "23.3.3.5"));
}

TEST(UnpackedArrayPortElaboration, InterfaceArrayAfterDeclarationsMatches) {
  EXPECT_TRUE(
      ElabOk("interface ifc; logic a; endinterface\n"
             "module user(ifc p[2]); endmodule\n"
             "module top;\n"
             "  logic v;\n"
             "  ifc ia[2]();\n"
             "  user u(ia);\n"
             "endmodule\n"));
}

TEST(UnpackedArrayPortsAndArraysOfInstancesElaboration,
     ATwoDimensionalInstanceArrayIsAnInstancePerElement) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output o, input i[5]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic o [8][4];\n"
      "  logic i [8][4][5];\n"
      "  child c[8][4](.o(o), .i(i));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  std::vector<std::string> names;
  for (const RtlirModuleInst& inst : design->top_modules.front()->children) {
    names.emplace_back(inst.inst_name);
  }
  ASSERT_EQ(names.size(), 32u);
  EXPECT_EQ(names.front(), "c[7][3]");
  EXPECT_EQ(names.back(), "c[0][0]");
  EXPECT_TRUE(std::ranges::find(names, "c[5][2]") != names.end());
}

}  // namespace
