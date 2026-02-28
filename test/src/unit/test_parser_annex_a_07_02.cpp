// Annex A.7.2: Specify path declarations

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.2 polarity_operator — combined forms
// =============================================================================
// Polarity with edge-sensitive full path
TEST(ParserA702, PolarityWithEdgeFullPath) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (negedge clk - *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_NE(si->path.data_source, nullptr);
}

}  // namespace
