// §30.4.4.3: Edge-sensitive state-dependent paths

#include "fixture_parser.h"

using namespace delta;

namespace {

// if (expr) edge_sensitive_path_declaration
TEST(ParserA702, StateDependentIfEdgeSensitive) {
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

}  // namespace
