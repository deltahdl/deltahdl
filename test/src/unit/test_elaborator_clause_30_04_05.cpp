#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FullAndParallelConnectionElaboration, VectorAndScalarEndpointsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input sel, input [7:0] in1, in2, output [7:0] q);\n"
      "  specify\n"
      "    (in1 => q) = 3;\n"
      "    (sel *> q) = 2;\n"
      "    (sel => sel) = 1;\n"
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

TEST(FullAndParallelConnectionElaboration, ErrorParallelScalarToVector) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output [7:0] b);\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
