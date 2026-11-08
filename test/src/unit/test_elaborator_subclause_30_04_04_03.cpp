#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EdgeSensitiveStateDependentPathElaboration,
     FullPathWithDataSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (en) (posedge clk *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     CoexistingUniqueByEdgeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (posedge clk => q) = 1;\n"
      "    if (c) (negedge clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     InconsistentPortReferenceIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk *> (q[3:0] : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk *> (q[0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "bit-select, or part-select)",
                            5, "30.4.4.3"));
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     EntirePortVsBitSelectIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk *> (q : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk *> (q[0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "bit-select, or part-select)",
                            5, "30.4.4.3"));
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     InconsistentSourceReferenceIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] clk, input reset, output q);\n"
      "  reg data;\n"
      "  specify\n"
      "    if (reset) (posedge clk[3:0] => (q : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk[0] => (q : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "bit-select, or part-select)",
                            5, "30.4.4.3"));
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     ConsistentPartSelectReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk *> (q[3:0] : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk *> (q[3:0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     DuplicateEdgeAndConditionIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input c, output q);\n"
      "  reg d;\n"
      "  specify\n"
      "    if (c) (posedge clk => (q : d)) = (10, 5);\n"
      "    if (c) (posedge clk => (q : d)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "must be made unique by edge, condition, or both",
                            5, "30.4.4.3"));
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     DistinctBitSelectPathsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input c, output [1:0] q);\n"
      "  reg d;\n"
      "  specify\n"
      "    if (c) (posedge clk => (q[0] : d)) = (10, 5);\n"
      "    if (c) (posedge clk => (q[1] : d)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     DuplicateBitSelectPathIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input c, output [1:0] q);\n"
      "  reg d;\n"
      "  specify\n"
      "    if (c) (posedge clk => (q[0] : d)) = (10, 5);\n"
      "    if (c) (posedge clk => (q[0] : d)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "must be made unique by edge, condition, or both",
                            5, "30.4.4.3"));
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     DuplicateParameterIndexPathIsIllegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input c, output [3:0] q);\n"
      "  localparam SEL = 1;\n"
      "  reg d;\n"
      "  specify\n"
      "    if (c) (posedge clk => (q[SEL] : d)) = (10, 5);\n"
      "    if (c) (posedge clk => (q[SEL] : d)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "must be made unique by edge, condition, or both",
                            6, "30.4.4.3"));
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     IndexedPartSelectReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk *> (q[1+:2] : data)) = (10, 5);\n"
      "    if (!reset) (posedge clk *> (q[1+:2] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EdgeSensitiveStateDependentPathElaboration,
     InconsistentReferenceAcrossSpecifyBlocksIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input clk, input reset, output [3:0] q);\n"
      "  reg [3:0] data;\n"
      "  specify\n"
      "    if (reset) (posedge clk *> (q[3:0] : data)) = (10, 5);\n"
      "  endspecify\n"
      "  specify\n"
      "    if (!reset) (posedge clk *> (q[0] : data)) = (15, 8);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "bit-select, or part-select)",
                            7, "30.4.4.3"));
}

}  // namespace
