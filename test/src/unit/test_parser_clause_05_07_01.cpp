// §5.7.1: Integer literal constants

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § octal_digit — 0 through 7
TEST(ParserA87, OctalDigitAll) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'o01234567; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 01234567u);
}

// § hex_digit — 0-9, a-f, A-F
TEST(ParserA87, HexDigitLowercase) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'habcdef; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDEFu);
}

TEST(ParserA87, HexDigitUppercase) {
  auto r =
      Parse("module m; logic [23:0] x; initial x = 24'hABCDEF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABCDEFu);
}

// § x_digit — x
TEST(ParserA87, XDigitLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'hx; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIntegerLiteral);
}

}  // namespace
