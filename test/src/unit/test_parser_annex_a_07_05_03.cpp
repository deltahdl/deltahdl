// Annex A.7.5.3: System timing check event definitions

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// scalar_timing_check_condition ::= ~ expression
TEST(ParserA70503, ScalarTimingCheckCondNegation) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& ~reset, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// scalar_timing_check_condition ::= expression == scalar_constant
TEST(ParserA70503, ScalarTimingCheckCondEquality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'b1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// scalar_timing_check_condition ::= expression != scalar_constant
TEST(ParserA70503, ScalarTimingCheckCondInequality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& (mode != 1'b0), data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// scalar_constant ::= 'b0
TEST(ParserA70503, ScalarConstantUnsized_b0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 'b0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
