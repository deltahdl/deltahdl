#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ArrayAddressingElaboration, WriteAndReadArrayElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin mem[0] = 8'h00; mem[2] = 8'hAB; end\n"
      "endmodule\n",
      f, "mem[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(ArrayAddressingElaboration, MultiDimArrayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] mem [0:3][0:3];\n"
             "  int result;\n"
             "  initial result = mem[1][2];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, MemoryIndirectionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] mem [0:7];\n"
             "  int result;\n"
             "  initial result = mem[mem[3]];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, BitSelectAfterArrayElementElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] arr [0:3];\n"
             "  logic result;\n"
             "  initial result = arr[2][5];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, PartSelectAfterAllDimensionsAddressed) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] twod [0:3][0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = twod[1][2][3:0];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, PartSelectAfterAllThreeDimensionsAddressed) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [3:0] result;\n"
             "  initial result = threed[2][1][0][3:0];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, AscendingSliceOfAnAscendingDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [31:0] result;\n"
             "  initial result = threed[2][1][0:3];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     DescendingSliceOfAnAscendingDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] threed [0:3][0:3][0:7];\n"
      "  logic [31:0] result;\n"
      "  initial result = threed[2][1][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

TEST(ArrayAddressingElaboration, DescendingSliceOfADescendingDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] dthreed [0:3][0:3][7:0];\n"
             "  logic [31:0] result;\n"
             "  initial result = dthreed[2][1][3:0];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     AscendingSliceOfADescendingDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] dthreed [0:3][0:3][7:0];\n"
      "  logic [31:0] result;\n"
      "  initial result = dthreed[2][1][0:3];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

TEST(ArrayAddressingElaboration, AscendingIndexedSliceOfADimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [31:0] result;\n"
             "  initial result = threed[2][1][0 +: 4];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, DescendingIndexedSliceOfADimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] threed [0:3][0:3][0:7];\n"
             "  logic [31:0] result;\n"
             "  initial result = threed[2][1][3 -: 4];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     DescendingSliceOfAnAscendingBitDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire threed_array [0:255][0:255][0:7];\n"
      "  wire [3:0] result;\n"
      "  assign result = threed_array[14][1][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

TEST(ArrayAddressingElaboration,
     AscendingSliceOfAnAscendingNetDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire threed_array [0:255][0:255][0:7];\n"
             "  wire [3:0] result;\n"
             "  assign result = threed_array[14][1][0:3];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, IndexingAnUnpackedNetArrayIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire w [3:0];\n"
             "  wire x;\n"
             "  assign x = w[1];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, IndexingAScalarNetIsStillIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  wire s;\n"
      "  wire x;\n"
      "  assign x = s[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            4, "11.5.1"));
}

TEST(ArrayAddressingElaboration, AssigningAVariableArrayToANetArrayIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] v[4];\n"
             "  wire [7:0] w[4];\n"
             "  assign w = v;\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, AscendingSliceOfASizedDimensionIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  initial r = A[1][0:1];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration, DescendingSliceOfASizedDimensionIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int A[2][3];\n"
      "  logic [63:0] r;\n"
      "  initial r = A[1][1:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice's first index must address a more significant element", 4,
      "11.5.2"));
}

TEST(ArrayAddressingElaboration,
     AscendingPartSelectOfAnAscendingElementIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [0:7] arr [0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = arr[2][0:3];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     DescendingPartSelectOfAnAscendingElementIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [0:7] arr [0:3];\n"
      "  logic [3:0] result;\n"
      "  initial result = arr[2][3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more "
                            "significant bit",
                            4, "11.5.1"));
}

TEST(ArrayAddressingElaboration,
     DescendingPartSelectOfADescendingElementIsLegal) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] darr [0:3];\n"
             "  logic [3:0] result;\n"
             "  initial result = darr[2][3:0];\n"
             "endmodule\n"));
}

TEST(ArrayAddressingElaboration,
     AscendingPartSelectOfADescendingElementIsIllegal) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] darr [0:3];\n"
      "  logic [3:0] result;\n"
      "  initial result = darr[2][0:3];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more "
                            "significant bit",
                            4, "11.5.1"));
}

TEST(ArrayAddressingElaboration, ReversedSliceInAForkArmNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  initial begin\n"
             "    fork\n"
             "      r = A[1][1:0];\n"
             "    join\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 6,
                            "11.5.2"));
}

TEST(ArrayAddressingElaboration,
     ReversedSliceInAnAssertionPassStatementNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  logic ok;\n"
             "  initial assert (ok) r = A[1][1:0];\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 5,
                            "11.5.2"));
}

TEST(ArrayAddressingElaboration,
     ReversedSliceInAnAssertionFailStatementNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  logic ok;\n"
             "  initial assert (ok) else r = A[1][1:0];\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 5,
                            "11.5.2"));
}

TEST(ArrayAddressingElaboration, ReversedSliceInARandcaseItemNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  initial randcase 1: r = A[1][1:0]; endcase\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 4,
                            "11.5.2"));
}

TEST(ArrayAddressingElaboration,
     ReversedSliceInARandsequenceCodeBlockNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : { r = A[1][1:0]; };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 6,
                            "11.5.2"));
}

TEST(ArrayAddressingElaboration,
     ReversedSliceInAForLoopInitializationNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  int i;\n"
             "  initial for (r = A[1][1:0]; i < 1; i = i + 1) ;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 5,
                            "11.5.2"));
}

TEST(ArrayAddressingElaboration, ReversedSliceInAForLoopStepNames11_5_2) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int A[2][3];\n"
             "  logic [63:0] r;\n"
             "  int i;\n"
             "  initial for (i = 0; i < 1; r = A[1][1:0]) ;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice's first index must address a more", 5,
                            "11.5.2"));
}

TEST(ArrayAddressingElaboration, BitSelectOfAScalarNetArrayElementIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w [0:3];\n"
      "  wire [7:0] w8 [0:3];\n"
      "  wire y, z;\n"
      "  assign y = w[1][0];\n"
      "  assign z = w8[1][0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            5, "11.5.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
