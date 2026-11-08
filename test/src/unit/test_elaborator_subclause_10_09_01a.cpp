#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayLiteralElaboration, SimpleArrayOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[1:0] = '{10, 20};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, NestedBracesOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { int a; int b; } ms_t;\n"
             "  ms_t ms[1:0] = '{'{0, 0}, '{1, 1}};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, DefaultKeyOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] arr [0:3];\n"
             "  initial arr = '{default: 8'd0};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, SizeMismatchError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int arr[1:0] = '{10, 20, 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            2, "10.9.1"));
}

TEST(ArrayLiteralElaboration, FlatInitIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern for an array of structures "
                            "shall nest a pattern per structure",
                            3, "5.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "assignment pattern has 4 elements, but array "
                             "dimension requires 2",
                             3, "10.9.1"));
}

TEST(ArrayLiteralElaboration, DuplicateIndexError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[0:2] = '{0: 1, 1: 2, 0: 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate index key '0' in array pattern", 2,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration, ReplicationOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:2] = '{3{0}};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, IndexKeyOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:2] = '{0: 10, 1: 20, 2: 30};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, PositionalArrayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [3];\n"
      "  initial arr = '{1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayLiteralElaboration, NarrowToWideElementOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:1] = '{1'b1, 1'b1};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, TypeKeyArrayOk) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[0:2] = '{int: 42};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, KeyedPatternUncoveredElementError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int arr[0:2] = '{0: 10, 2: 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            2, "10.9.1"));
}

TEST(ArrayLiteralElaboration, BitElementNoSizeWarning) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  bit arr[1:0] = '{1, 1};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, ArrayItemInPatternInAForkArmNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  initial begin\n"
      "    fork\n"
      "      A2 = '{A3, A3};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 7,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration,
     ArrayItemInPatternInAnAssertionPassStatementNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  logic ok;\n"
      "  initial assert (ok) A2 = '{A3, A3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 6,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration,
     ArrayItemInPatternInAnAssertionFailStatementNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  logic ok;\n"
      "  initial assert (ok) else A2 = '{A3, A3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 6,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration, ArrayItemInPatternInARandcaseItemNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  initial randcase 1: A2 = '{A3, A3}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 5,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration,
     ArrayItemInPatternInARandsequenceCodeBlockNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { A2 = '{A3, A3}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 7,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration,
     ArrayItemInPatternInAForLoopInitializationNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  int i;\n"
      "  initial for (A2 = '{A3, A3}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 6,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration, ArrayItemInPatternInAForLoopStepNames10_9_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int AI3[1:3];\n"
      "  AI3 A3;\n"
      "  int A2[1:2];\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; A2 = '{A3, A3}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array-typed identifier in assignment pattern", 6,
                            "10.9.1"));
}

TEST(ArrayLiteralElaboration, TypeKeyThatCannotMatchDoesNotCoverTheArray) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[0:2] = '{int: 8'h05};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            2, "10.9.1"));
}

TEST(ArrayLiteralElaboration, TypeKeyMatchingTheElementTypeCoversTheArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic arr[0:2] = '{logic: 1'b1};\n"
             "  bit signed [7:0] brr[0:1] = '{byte: 8'h05};\n"
             "endmodule\n"));
}

TEST(ArrayLiteralElaboration, TypeKeyCoversEveryDimensionOfAMultidimArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[0:1][0:1] = '{int: 5};\n"
             "endmodule\n"));
}

TEST(ArrayPatternElaboration, TypedefTypeKeyCoversElements) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef logic [7:0] byte_t;\n"
      "module m;\n"
      "  byte_t arr[3] = '{byte_t: 8'h1};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArrayPatternElaboration, TypeKeyMatchesByFullType) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int myint;\n"
      "module m;\n"
      "  myint arr[3] = '{int: 5};\n"
      "  logic [7:0] b[2] = '{logic: 1'b1};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "keyed array pattern does not cover all elements",
                             3, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            4, "10.9.1"));
}

TEST(ArrayPatternElaboration, NestedPatternCountedAgainstItsDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a[2][3] = '{'{1, 2}, '{3, 4, 5}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            2, "10.9.1"));
}

TEST(ArrayPatternElaboration, TypeKeyCoversStructureElementsByMembers) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct { int x, y; } s_t;\n"
      "typedef struct { int x; byte y; } t_t;\n"
      "module m;\n"
      "  s_t arr[2] = '{int: 7};\n"
      "  t_t brr[2] = '{int: 7};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "keyed array pattern does not cover all elements",
                             4, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            5, "10.9.1"));
}

TEST(ArrayPatternElaboration, PackedVariableInitCountedAgainstPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] v = '{1'b1, 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            2, "10.9.1"));
}

TEST(ArrayPatternElaboration, PackedPatternsMatchingTheirDimensionsElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [3:0] v = '{1'b1, 1'b0, 1'b1, 1'b1};\n"
             "  logic [1:0][3:0] w = '{'{1'b1, 1'b0, 1'b1, 1'b1}, 4'h2};\n"
             "  logic [7:0] r = '{8{1'b1}};\n"
             "  logic [3:0] d = '{default: 1'b0};\n"
             "  logic [3:0] k = '{logic: 1'b1};\n"
             "endmodule\n"));
}

TEST(ArrayPatternElaboration, NestedPatternCountedAgainstInnerPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0][3:0] w = '{'{1'b1, 1'b0}, 4'h2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            2, "10.9.1"));
}

TEST(ArrayPatternElaboration, ElementPatternCountedAgainstPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a [2] = '{'{1'b1, 1'b0, 1'b1}, 4'h0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 4",
                            2, "10.9.1"));
}

TEST(ArrayPatternElaboration, ProceduralPatternCountedAgainstPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0][3:0] w;\n"
      "  initial w = '{4'h1, 4'h2, 4'h3};\n"
      "  initial begin\n"
      "    static logic [3:0] b = '{1'b1};\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            3, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 1 elements, but array "
                            "dimension requires 4",
                            5, "10.9.1"));
}

TEST(ArrayPatternElaboration, TypedefPackedDimensionsCounted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  nib_t [1:0] w = '{'{1'b1, 1'b0}, 4'h0};\n"
      "  nib_t v = '{1'b1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            3, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 1 elements, but array "
                            "dimension requires 4",
                            4, "10.9.1"));
}

TEST(ArrayPatternElaboration, TypedefUnpackedDimensionsComeBeforePackedOnes) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef logic [3:0] row_t [2];\n"
             "  row_t a [3] = '{'{4'h1, 4'h2}, '{4'h3, 4'h4}, '{4'h5, 4'h6}};\n"
             "  initial begin\n"
             "    static row_t r = '{4'h1, 4'h2};\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ArrayPatternElaboration, PackageScopedTypePackedDimensionCounted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef logic [3:0] nib_t;\n"
      "endpackage\n"
      "module m;\n"
      "  initial begin\n"
      "    static p::nib_t [1:0] w = '{4'h1, 4'h2, 4'h3};\n"
      "  end\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            6, "10.9.1"));
}

TEST(ArrayPatternElaboration, KeyedPackedPatternUncoveredElementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] v = '{0: 1'b1, 1: 1'b0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "keyed array pattern does not cover all elements",
                            2, "10.9.1"));
}

TEST(ArrayPatternElaboration, PortConnectionCountedAgainstPackedDimension) {
  ElabFixture f;
  ElaborateSrc(
      "module sc(input logic [15:0] p);\n"
      "endmodule\n"
      "module sa(input logic [3:0] p [2]);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  logic [3:0] rows [2];\n"
      "  sc u1(.p('{x, y}));\n"
      "  sc u2(.p('{16{x}}));\n"
      "  sa u3(.p(rows));\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 16",
                            8, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ArrayPatternElaboration, ContinuousAssignmentPatternCountedAgainstTarget) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w [0:2];\n"
      "  assign w = '{8'h1, 8'h2};\n"
      "  logic [3:0] v;\n"
      "  assign v = '{1'b1, 1'b0};\n"
      "  int a [2][3];\n"
      "  assign a = '{'{1, 2}, '{3, 4, 5}};\n"
      "  wire [3:0] n = '{1'b1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            3, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            5, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            7, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 1 elements, but array "
                            "dimension requires 4",
                            8, "10.9.1"));
}

TEST(ArrayPatternElaboration, ContinuousAssignmentPatternMatchingTargetOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire [7:0] w [0:2];\n"
             "  assign w = '{8'h1, 8'h2, 8'h3};\n"
             "  logic [3:0] v;\n"
             "  assign v = '{4{1'b1}};\n"
             "  wire [3:0] n = '{1'b1, 1'b0, 1'b1, 1'b0};\n"
             "endmodule\n"));
}

TEST(ArrayPatternElaboration, PortOfPackedTypedefCountedAgainstItsDimension) {
  ElabFixture f;
  ElaborateSrc(
      "typedef logic [3:0] nib_t;\n"
      "module sub(input nib_t p);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  sub u1(.p('{x, y}));\n"
      "  sub u2(.p('{x, y, x, y}));\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            6, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ArrayPatternElaboration, PortWithUnpackedDimensionsCountedAgainstThem) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(input var int p [0:1]);\n"
      "endmodule\n"
      "module sa(input logic [3:0] q [2]);\n"
      "endmodule\n"
      "module top;\n"
      "  sub u(.p('{5, 6, 7}));\n"
      "  sa v(.q('{'{1'b1, 1'b0}, 4'h0}));\n"
      "  sd w(.d('{1, 2, 3}));\n"
      "endmodule\n"
      "module sd(input var int d []);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            6, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            7, "10.9.1"));
}

}  // namespace
