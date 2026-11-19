#include <gtest/gtest.h>

#include <string>

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

void ExpectEdgePathAccepted(const std::string& ports, const std::string& path) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m(" + ports +
                                  ");\n"
                                  "  specify\n"
                                  "    " +
                                  path +
                                  "\n"
                                  "  endspecify\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

void ExpectEdgePathReported(const std::string& ports, const std::string& path,
                            const std::string& message) {
  ElabFixture f;
  ElaborateSrc("module m(" + ports +
                   ");\n"
                   "  specify\n"
                   "    " +
                   path +
                   "\n"
                   "  endspecify\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, "30.4.3"));
}

constexpr const char* kEdgePorts =
    "input clk, input d, output [3:0] q, output r, inout b, inout [3:0] v";

TEST(SpecifyPathElaboration, EdgeFullPathToAVectorAndAScalarElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(posedge clk *> (q, r : d)) = 10;");
}

TEST(SpecifyPathElaboration, EdgeFullPathToAWholeVectorElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(posedge clk *> (q : d)) = 10;");
}

TEST(SpecifyPathElaboration, EdgeFullPathToAScalarElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(posedge clk *> (r : d)) = 10;");
}

TEST(SpecifyPathElaboration, EdgeFullPathToAScalarInoutElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(negedge clk *> (b : d)) = 10;");
}

TEST(SpecifyPathElaboration, EdgeFullPathToAVectorInoutElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(negedge clk *> (v : d)) = 10;");
}

TEST(SpecifyPathElaboration, EdgeFullPathToAnInoutPartSelectElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(edge clk *> (v[2:1] : d)) = 10;");
}

TEST(SpecifyPathElaboration, EdgeFullPathToAnOutputBitSelectElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(posedge clk *> (q[2] : d)) = 10;");
}

TEST(SpecifyPathElaboration, EdgeFullPathToAMixedDestinationListElaborates) {
  ExpectEdgePathAccepted(kEdgePorts,
                         "(posedge clk *> (q[1], q[3:2], r, v[0], b : d)) = "
                         "10;");
}

TEST(SpecifyPathElaboration, EdgeFullPathWithoutDataSourceToAVectorElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(posedge clk *> q, r) = 10;");
}

TEST(SpecifyPathElaboration, EdgeParallelPathToAScalarInoutElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(posedge clk => (b : d)) = 1;");
}

TEST(SpecifyPathElaboration, EdgeParallelPathToAnInoutBitSelectElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "(posedge clk => (v[1] : d)) = 1;");
}

TEST(SpecifyPathElaboration, EdgeParallelPathToAVectorInoutIsRejected) {
  ExpectEdgePathReported(kEdgePorts, "(posedge clk => (v : d)) = 1;",
                         "destination 'v' of an edge-sensitive parallel path "
                         "is a vector");
}

TEST(SpecifyPathElaboration, EdgeParallelPathToAnInoutPartSelectIsRejected) {
  ExpectEdgePathReported(kEdgePorts, "(posedge clk => (v[2:1] : d)) = 1;",
                         "destination 'v' of an edge-sensitive parallel path "
                         "is a part-select");
}

TEST(SpecifyPathElaboration, ConditionalEdgeParallelPathToAVectorIsRejected) {
  ExpectEdgePathReported(kEdgePorts, "if (d) (posedge clk => (q : d)) = 1;",
                         "destination 'q' of an edge-sensitive parallel path "
                         "is a vector");
}

TEST(SpecifyPathElaboration, ConditionalEdgeParallelPartSelectIsRejected) {
  ExpectEdgePathReported(kEdgePorts,
                         "if (d) (posedge clk => (q[1:0] : d)) = 1;",
                         "destination 'q' of an edge-sensitive parallel path "
                         "is a part-select");
}

TEST(SpecifyPathElaboration, ConditionalEdgeParallelBitSelectElaborates) {
  ExpectEdgePathAccepted(kEdgePorts, "if (d) (posedge clk => (q[0] : d)) = 1;");
}

}  // namespace
