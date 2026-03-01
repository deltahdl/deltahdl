// Annex A.7.5.2: System timing check command arguments

#include "fixture_parser.h"

using namespace delta;

namespace {

// delayed_data ::= terminal_identifier [ constant_mintypmax_expression ]
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

}  // namespace
