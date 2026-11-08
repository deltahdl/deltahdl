#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssocArrayOperandElaboration, AssocOperandInAForkArmNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial begin\n"
      "    fork\n"
      "      x = aa + 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 6,
                            "7.4.6"));
}

TEST(AssocArrayOperandElaboration,
     AssocOperandInAnAssertionPassStatementNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = aa + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 5,
                            "7.4.6"));
}

TEST(AssocArrayOperandElaboration,
     AssocOperandInAnAssertionFailStatementNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = aa + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 5,
                            "7.4.6"));
}

TEST(AssocArrayOperandElaboration, AssocOperandInARandcaseItemNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial randcase 1: x = aa + 1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 4,
                            "7.4.6"));
}

TEST(AssocArrayOperandElaboration,
     AssocOperandInARandsequenceCodeBlockNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = aa + 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 6,
                            "7.4.6"));
}

TEST(AssocArrayOperandElaboration,
     AssocOperandInAForLoopInitializationNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (x = aa + 1; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 5,
                            "7.4.6"));
}

TEST(AssocArrayOperandElaboration, AssocOperandInAForLoopStepNames7_4_6) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; x = aa + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 5,
                            "7.4.6"));
}

TEST(UnpackedArrayOperandElaboration, AnUnpackedArrayIsNoIntegralOperand) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int m[2][3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == 4) x = 1;\n"
      "    if (m[1] != 4) x = 2;\n"
      "    x = a + 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an unpacked array is not an operand of this "
                            "operator",
                            8, "7.4.6"));
}

TEST(UnpackedArrayOperandElaboration, EveryIntegralOperandKindIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == '1) x = 1;\n"
      "    if (a != 1.5) x = 2;\n"
      "    if (a == x + 1) x = 3;\n"
      "    if (-x != a) x = 4;\n"
      "    x = -a;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 5, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 8, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an unpacked array is not an operand of this "
                            "operator",
                            9, "7.4.6"));
}

TEST(UnpackedArrayOperandElaboration, ArraysComparedWithArraysAreAllowed) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3], b[3];\n"
      "  int m[2][3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == b) x = 1;\n"
      "    if (a[0:1] != b[1:2]) x = 2;\n"
      "    if (m[1] == m[0]) x = 3;\n"
      "    if (a[2] == 4) x = x + a[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnpackedArrayOperandElaboration, IntegralVariablesAreNoArrays) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  int a[3];\n"
      "  int x;\n"
      "  byte_t v;\n"
      "  logic [3:0] w;\n"
      "  initial begin\n"
      "    int y;\n"
      "    if (a == x) x = 1;\n"
      "    if (v != a) x = 2;\n"
      "    if (a === w) x = 3;\n"
      "    if (a == y) x = 4;\n"
      "    for (int i = 0; i < 3; i++) if (a == i) x = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  for (int line = 9; line <= 13; ++line) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, line, "7.4.6"))
        << "line " << line;
  }
}

TEST(UnpackedArrayOperandElaboration, AnEqualityResultIsNoArray) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == (x == 1)) x = 1;\n"
      "    if ((x !== 1) != a) x = 2;\n"
      "    if (a == (x ==? 1)) x = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 5, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
}

TEST(UnpackedArrayOperandElaboration, BlockDeclarationsHideTheModules) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef int row_t[3];\n"
      "  int a[3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    int a;\n"
      "    if (a == 4) x = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    int x[3];\n"
      "    row_t r;\n"
      "    if (a == x) x[0] = 1;\n"
      "    if (a == r) x[0] = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnpackedArrayOperandElaboration, BlockArraysAreNoIntegralOperands) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    int b[3];\n"
      "    int q[$];\n"
      "    if (b == 4) x = 1;\n"
      "    x = b + 1;\n"
      "    if (q != x) x = 2;\n"
      "    if (b[1] == 4) x = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an unpacked array is not an operand of this "
                            "operator",
                            7, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 8, "7.4.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kCompared, 9, "7.4.6"));
}

TEST(UnpackedArrayOperandElaboration, AssociativeArraysAreNoIntegralOperands) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  initial begin\n"
      "    int ab[int];\n"
      "    if (aa == 4) x = 1;\n"
      "    if (x != ab) x = 2;\n"
      "    if (aa == ab) x = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 6, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kCompared, 8, "7.4.6"));
}

TEST(AssocArrayOperandElaboration, BlockDeclarationsAreSeenInScope) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int x;\n"
      "  initial begin\n"
      "    int ab[string];\n"
      "    x = ab + 1;\n"
      "  end\n"
      "  initial begin\n"
      "    int aa;\n"
      "    x = aa + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array operand requires an element", 6,
                            "7.4.6"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "associative array operand requires an element",
                             10, "7.4.6"));
}

TEST(UnpackedArrayOperandElaboration, NetsAreNoArrays) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  wire [3:0] w;\n"
      "  wire logic v;\n"
      "  int x;\n"
      "  initial begin\n"
      "    if (a == w) x = 1;\n"
      "    if (v != a) x = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kCompared =
      "an unpacked array is compared only with another unpacked array";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 7, "7.4.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kCompared, 8, "7.4.6"));
}

}  // namespace
