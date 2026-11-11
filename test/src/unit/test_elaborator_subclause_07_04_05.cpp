#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayIndexingElaboration, IndexedPartSelectWidthParameterAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  parameter W = 8;\n"
             "  logic [31:0] vec;\n"
             "  logic [7:0] res;\n"
             "  int base;\n"
             "  initial res = vec[base +: W];\n"
             "endmodule\n"));
}

TEST(ArrayIndexingElaboration, IndexedPartSelectWidthLocalparamAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  localparam W = 4;\n"
             "  logic [31:0] vec;\n"
             "  logic [3:0] res;\n"
             "  int base;\n"
             "  initial res = vec[base -: W];\n"
             "endmodule\n"));
}

TEST(ArrayIndexingElaboration, NonConstantPartSelectWidthRejected) {
  ElabFixture f;
  ElabOk(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] res;\n"
      "  int base;\n"
      "  int n;\n"
      "  initial res = vec[base +: n];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 6, "11.5.1"));
}

constexpr std::string_view kIndexedWidth =
    "indexed part-select width must be a constant expression";
constexpr std::string_view kNonIndexedBounds =
    "non-indexed part-select bounds shall be constant expressions";

TEST(ArrayIndexingElaboration,
     NonConstantSliceWidthReportedInModuleProceduresAndContinuousAssignments) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int busA [7:0];\n"
      "  int busB [1:0];\n"
      "  int busC [1:0];\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] r;\n"
      "  int x, y;\n"
      "  wire [7:0] w = vec[x:y];\n"
      "  wire [7:0] wok = vec[x +: 8];\n"
      "  always_comb busC = busA[x +: y];\n"
      "  initial begin\n"
      "    busB = busA[x -: y];\n"
      "    r = vec[x:y];\n"
      "    r = vec[x +: 8];\n"
      "    busB = busA[x +: 2];\n"
      "    busB = busA[7:6];\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {10, 12}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kIndexedWidth, line, "11.5.1"))
        << line;
  }
  for (uint32_t line : {8, 13}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNonIndexedBounds, line, "11.5.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(
    ArrayIndexingElaboration,
    DISABLED_NonConstantSliceWidthReportedInSubroutinesClassesPackagesAndUnpackedRanges) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  function automatic void pf(int x, int y);\n"
      "    int a [8];\n"
      "    int b [2];\n"
      "    b = a[x +: y];\n"
      "    b = a[x +: 2];\n"
      "  endfunction\n"
      "endpackage\n"
      "class K;\n"
      "  int a [8];\n"
      "  int b [2];\n"
      "  function void m(int x, int y);\n"
      "    b = a[x -: y];\n"
      "    b = a[x -: 2];\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  int busA [7:0];\n"
      "  int busB [1:0];\n"
      "  int x, y;\n"
      "  function automatic void f();\n"
      "    busB = busA[x +: y];\n"
      "    busB = busA[x:y];\n"
      "    busB = busA[x +: 2];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    busB = busA[x:y];\n"
      "    busB = busA[7:6];\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5, 13, 22}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kIndexedWidth, line, "11.5.1"))
        << line;
  }
  for (uint32_t line : {23, 27}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNonIndexedBounds, line, "11.5.1"))
        << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 5u);
}

}  // namespace
