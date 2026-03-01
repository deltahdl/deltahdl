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

// 2 delays: trise, tfall
TEST(ParserA704, ListOfPathDelayExpr2) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (3, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 2u);
}

// 3 delays: trise, tfall, tz
TEST(ParserA704, ListOfPathDelayExpr3) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (2, 3, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 3u);
}

}  // namespace
