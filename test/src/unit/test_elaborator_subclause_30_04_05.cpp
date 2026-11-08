#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FullAndParallelConnectionElaboration, VectorAndScalarEndpointsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parallel path source and destination must have "
                            "equal bit widths",
                            3, "30.4.5"));
}

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
