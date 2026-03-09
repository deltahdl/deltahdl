#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA70502, DelayedDataWithBracketExpr) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dD[3]);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->delayed_data, "dD");
  EXPECT_NE(tc->delayed_data_expr, nullptr);
}

TEST(ParserA70502, DelayedReferenceWithBracketExpr) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK[1:2:3], dD);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->delayed_ref, "dCLK");
  ASSERT_NE(tc->delayed_ref_expr, nullptr);
  EXPECT_EQ(tc->delayed_ref_expr->kind, ExprKind::kMinTypMax);
}

TEST(ParserA70502, ThresholdExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20, 1);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_GE(tc->limits.size(), 2u);
}

TEST(TimingCheckLimitExpression, TimingCheckLimitExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_NE(tc->limits[0], nullptr);
}

}  // namespace
