#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FullAndParallelConnectionElaboration, VectorAndScalarEndpointsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      // 30.3.1: a module path destination shall be connected to an output or
      // inout port; the scalar endpoint path drives the scalar output qs (the
      // input sel would be an illegal destination).
      "module m(input sel, input [7:0] in1, in2, output [7:0] q,\n"
      "         output qs);\n"
      "  specify\n"
      "    (in1 => q) = 3;\n"
      "    (sel *> q) = 2;\n"
      "    (sel => qs) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration, FullAllowsDifferentWidthVectors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [3:0] b);\n"
      "  specify\n"
      "    (a *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration, FullAllowsVectorToScalar) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output b);\n"
      "  specify\n"
      "    (a *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration, ScalarPairAcceptsEitherOperator) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 1;\n"
      "    (a *> b) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FullAndParallelConnectionElaboration, ErrorParallelWidthMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [7:0] a, output [3:0] b);\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.5: a parallel connection requires equal bit counts. Here the endpoints
// are part-selects (Syntax 30-3 constant_range_expression) rather than whole
// ports, so the equal-width rule is decided from the selected ranges: [5:2] and
// [3:0] both name four bits, so the parallel path is legal.
TEST(FullAndParallelConnectionElaboration, ParallelEqualWidthPartSelects) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[5:2] => b[3:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.5: the same part-select terminals, but now the selected ranges differ
// in width (four bits versus two), so the parallel connection is rejected even
// though both endpoints are eight-bit ports.
TEST(FullAndParallelConnectionElaboration,
     ErrorParallelPartSelectWidthMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[5:2] => b[1:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.5: full connections carry no width constraint, so the width-mismatched
// part-selects that the parallel rule rejects above are accepted under '*>'.
TEST(FullAndParallelConnectionElaboration, FullAllowsPartSelectWidthMismatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[5:2] *> b[1:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.5: a bit-select names exactly one bit, so a parallel path between two
// bit-selects is one-bit-to-one-bit and satisfies the equal-width rule
// regardless of which bit each names.
TEST(FullAndParallelConnectionElaboration, ParallelBitSelectsEqualWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[3] => b[5]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.5 negative: a one-bit bit-select source cannot form a parallel path to
// a two-bit part-select destination.
TEST(FullAndParallelConnectionElaboration,
     ErrorParallelBitSelectWidthMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[3] => b[1:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.5: an indexed part-select ([base+:width]) selects `width` bits, so two
// four-bit plus-indexed selects form a legal equal-width parallel path.
TEST(FullAndParallelConnectionElaboration, ParallelPlusIndexedEqualWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[0+:4] => b[3:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.5 negative: a four-bit plus-indexed source against a two-bit
// destination violates the equal-width rule.
TEST(FullAndParallelConnectionElaboration,
     ErrorParallelPlusIndexedWidthMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[0+:4] => b[1:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §30.4.5: the minus-indexed part-select ([base-:width]) likewise selects
// `width` bits, so a four-bit minus-indexed source matches a four-bit
// destination.
TEST(FullAndParallelConnectionElaboration, ParallelMinusIndexedEqualWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] b);\n"
      "  specify\n"
      "    (a[3-:4] => b[3:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
