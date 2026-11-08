#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BitStreamCastElaboration, IntToPackedStructOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p = pair_t'(16'hCAFE);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BitStreamCastElaboration, UnpackedArrayMatchingSizeOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte arr [4];\n"
      "  int result;\n"
      "  initial result = int'(arr);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BitStreamCastElaboration, AssociativeArrayDestRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte amap_t [string];\n"
      "  byte src;\n"
      "  amap_t dst;\n"
      "  initial dst = amap_t'(src);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array type 'amap_t' is illegal as a "
                            "bit-stream cast destination",
                            5, "6.24.3"));
}

TEST(BitStreamCastElaboration, WildcardAssocDestRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte wmap_t [*];\n"
      "  byte src;\n"
      "  wmap_t dst;\n"
      "  initial dst = wmap_t'(src);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array type 'wmap_t' is illegal as a "
                            "bit-stream cast destination",
                            5, "6.24.3"));
}

TEST(BitStreamCastElaboration, ClassKeyedAssocDestRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Key;\n"
      "endclass\n"
      "module m;\n"
      "  typedef byte kmap_t [Key];\n"
      "  byte src;\n"
      "  kmap_t dst;\n"
      "  initial dst = kmap_t'(src);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array type 'kmap_t' is illegal as a "
                            "bit-stream cast destination",
                            7, "6.24.3"));
}

TEST(BitStreamCastElaboration, ClassDestFromNonClassRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Container;\n"
      "endclass\n"
      "module m;\n"
      "  int src;\n"
      "  Container c;\n"
      "  initial c = Container'(src);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot cast non-class value to a class type", 6,
                            "8.4"));
}

TEST(BitStreamCastElaboration, ClassWithLocalSourceRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Hidden;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Hidden h;\n"
      "  int v;\n"
      "  initial v = int'(h);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class handle 'h' is illegal as a bit-stream cast "
                            "source: its class has local or protected members",
                            7, "6.24.3"));
}

TEST(BitStreamCastElaboration, ClassWithProtectedSourceRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class Hidden;\n"
      "  protected int hidden;\n"
      "endclass\n"
      "module m;\n"
      "  Hidden h;\n"
      "  int v;\n"
      "  initial v = int'(h);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class handle 'h' is illegal as a bit-stream cast "
                            "source: its class has local or protected members",
                            7, "6.24.3"));
}

TEST(BitStreamCastElaboration, FixedSizeMismatchUnpackedRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  initial result = int'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            4, "6.24.3"));
}

TEST(BitStreamCastElaboration, UnpackedToStructWrongWidthRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } "
      "pair_t;\n"
      "  byte arr [3];\n"
      "  pair_t p;\n"
      "  initial p = pair_t'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 16 bits) with an "
                            "unpacked operand is illegal",
                            5, "6.24.3"));
}

TEST(BitStreamCastElaboration, ContAssignFixedSizeMismatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  assign result = int'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            4, "6.24.3"));
}

TEST(BitStreamCastElaboration, FixedSizeMismatchUnpackedDestRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte arr4_t [4];\n"
      "  arr4_t a;\n"
      "  initial a = arr4_t'(16'hABCD);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (16 bits to 32 bits) with an "
                            "unpacked destination is illegal",
                            4, "6.24.3"));
}

TEST(BitStreamCastElaboration, FixedSizeMatchUnpackedDestOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef byte arr4_t [4];\n"
      "  arr4_t a;\n"
      "  initial a = arr4_t'(32'hDEADBEEF);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BitStreamCastElaboration,
     StreamSourceNarrowerThanUnpackedDestinationRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte arr2_t [2];\n"
      "  arr2_t a;\n"
      "  initial a = arr2_t'({>> {4'b1100}});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (4 bits to 16 bits) with an "
                            "unpacked destination is illegal",
                            4, "6.24.3"));
}

TEST(BitStreamCastElaboration, StreamSourceMatchingUnpackedDestinationWidthOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef byte arr2_t [2];\n"
      "  arr2_t a;\n"
      "  initial a = arr2_t'({>> {8'hAB, 8'hCD}});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BitStreamCastElaboration, FixedSizeMismatchInAForkStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  initial fork\n"
      "    result = int'(arr);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            5, "6.24.3"));
}

TEST(BitStreamCastElaboration, FixedSizeMismatchInAForInitializerRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  int i;\n"
      "  initial\n"
      "    for (result = int'(arr); i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            6, "6.24.3"));
}

TEST(BitStreamCastElaboration, FixedSizeMismatchInAForStepRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; result = int'(arr))\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            6, "6.24.3"));
}

TEST(BitStreamCastElaboration,
     FixedSizeMismatchInAnAssertionPassStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  logic ok;\n"
      "  initial assert (ok) result = int'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            5, "6.24.3"));
}

TEST(BitStreamCastElaboration,
     FixedSizeMismatchInAnAssertionFailStatementRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  logic armed;\n"
      "  initial assert (armed) else result = int'(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            5, "6.24.3"));
}

TEST(BitStreamCastElaboration, FixedSizeMismatchInARandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  initial randcase 1: result = int'(arr); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            4, "6.24.3"));
}

TEST(BitStreamCastElaboration,
     FixedSizeMismatchInARandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  byte arr [3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { result = int'(arr); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            6, "6.24.3"));
}

TEST(BitStreamCastElab, UnpackedArrayMemberCountsEveryElement) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { shortint address; logic [3:0] code;\n"
             "                   byte command [2]; } Control;\n"
             "  typedef bit Bits [36:1];\n"
             "  Control p, q; Bits b;\n"
             "  initial begin\n"
             "    b = Bits'(p);\n"
             "    q = Control'(b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(BitStreamCastElab, UnpackedArrayMemberSizeMismatchStillReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { shortint address; logic [3:0] code;\n"
      "                   byte command [2]; } Control;\n"
      "  typedef bit Bits [28:1];\n"
      "  Control q; Bits b;\n"
      "  initial q = Control'(b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (28 bits to 36 bits) with an "
                            "unpacked operand is illegal",
                            6, "6.24.3"));
}

TEST(BitStreamCastElab, UnpackedStructOperandOfAnotherSizeReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct { bit [7:0] a; shortint b; } a;\n"
      "  int b;\n"
      "  initial b = int'(a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast between fixed-size types of "
                            "different sizes (24 bits to 32 bits) with an "
                            "unpacked operand is illegal",
                            4, "6.24.3"));
}

TEST(BitStreamCastElab, UnpackedStructOperandOfTheSameSizeAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  struct { shortint a; shortint b; } a;\n"
             "  int b;\n"
             "  initial b = int'(a);\n"
             "endmodule\n"));
}

TEST(BitStreamCastElab, UnpackedStructOperandWithAStringIsNotSizedHere) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct {int n; string s;} pair_t;\n"
             "  typedef bit [47:0] b48_t;\n"
             "  pair_t p;\n"
             "  b48_t b;\n"
             "  initial b = b48_t'(p);\n"
             "endmodule\n"));
}

}  // namespace
