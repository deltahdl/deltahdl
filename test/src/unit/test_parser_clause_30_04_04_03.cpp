#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(EdgeSensitiveStateDependentPathParsing, ParallelPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
}

TEST(EdgeSensitiveStateDependentPathParsing, FullPathWithDataSource) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (posedge clk *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_NE(si->path.data_source, nullptr);
}

TEST(EdgeSensitiveStateDependentPathParsing, ParallelNegedgePath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (en) (negedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
}

TEST(EdgeSensitiveStateDependentPathParsing, CoexistingUniqueByEdge) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (c) (posedge clk => q) = 1;\n"
      "    if (c) (negedge clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(EdgeSensitiveStateDependentPathParsing, CoexistingUniqueByCondition) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (c1) (posedge clk => q) = 1;\n"
      "    if (c2) (posedge clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(EdgeSensitiveStateDependentPathParsing, CoexistingConsistentBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    if (c) (posedge clk => q[0]) = 1;\n"
      "    if (c) (negedge clk => q[0]) = 2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
