// Annex A.7.4: Specify path delays

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.4 list_of_path_delay_expressions — 1, 2, 3, 6, 12 delays
// =============================================================================
// 1 delay: t_path_delay_expression
TEST(ParserA704, ListOfPathDelayExpr1) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

}  // namespace
