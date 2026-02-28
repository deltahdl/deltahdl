// §31.7: Enabling timing checks with conditioned events

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// scalar_timing_check_condition ::= expression === scalar_constant
TEST(ParserA70503, ScalarTimingCheckCondCaseEquality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en === 1'b1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// scalar_timing_check_condition ::= expression !== scalar_constant
TEST(ParserA70503, ScalarTimingCheckCondCaseInequality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& (mode !== 1'b0), data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// =============================================================================
// A.7.5.3 scalar_constant
// =============================================================================
// scalar_constant ::= 1'b0
TEST(ParserA70503, ScalarConstant1b0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'b0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// scalar_constant ::= 1'B1
TEST(ParserA70503, ScalarConstant1B1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'B1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// scalar_constant ::= 1
TEST(ParserA70503, ScalarConstantDecimal1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
