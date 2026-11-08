#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SpecifyPathElaboration, EdgeSensitivePathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathElaboration, EdgeSensitiveWithDataSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathElaboration, EdgeParallelPathToAVectorIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clk, input [3:0] d, output [3:0] q);\n"
      "  specify\n"
      "    (posedge clk => (q : d)) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "destination 'q' of an edge-sensitive parallel "
                            "path is a vector",
                            3, "30.4.3"));
}

TEST(SpecifyPathElaboration, EdgeParallelPathBetweenEqualVectorsIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [3:0] c, output [3:0] r);\n"
      "  specify\n"
      "    (negedge c => r) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "destination 'r' of an edge-sensitive parallel "
                            "path is a vector",
                            3, "30.4.3"));
}

TEST(SpecifyPathElaboration, EdgeParallelPathToAPartSelectIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clk, d, output [3:0] q);\n"
      "  specify\n"
      "    (posedge clk => (q[1:0] : d)) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "destination 'q' of an edge-sensitive parallel "
                            "path is a part-select",
                            3, "30.4.3"));
}

TEST(SpecifyPathElaboration, EdgeParallelPathFromAVectorToAScalarElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] c, output q);\n"
      "  specify\n"
      "    (posedge c => q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathElaboration, EdgeParallelPathToABitSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] c, input d, output [3:0] q);\n"
      "  specify\n"
      "    (posedge c => (q[2] : d)) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
