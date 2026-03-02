// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// § binary_base — 'B
TEST(ParserA87, BinaryBaseUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'B1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

// § binary_base — 'sb (signed)
TEST(ParserA87, BinaryBaseSignedLower) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'sb1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

// § binary_base — 'SB
TEST(ParserA87, BinaryBaseSignedUpper) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'SB1111; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xFu);
}

// § octal_base — 'o
TEST(ParserA87, OctalBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'o77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § octal_base — 'O
TEST(ParserA87, OctalBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'O77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § octal_base — 'so (signed)
TEST(ParserA87, OctalBaseSignedLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'so77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § octal_base — 'SO
TEST(ParserA87, OctalBaseSignedUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SO77; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 077u);
}

// § hex_base — 'h
TEST(ParserA87, HexBaseLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'hAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

// § hex_base — 'H
TEST(ParserA87, HexBaseUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'HAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

// § hex_base — 'sh (signed)
TEST(ParserA87, HexBaseSignedLower) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'shAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

// § hex_base — 'SH
TEST(ParserA87, HexBaseSignedUpper) {
  auto r = Parse("module m; logic [7:0] x; initial x = 8'SHAB; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 0xABu);
}

// § decimal_digit — 0 through 9
TEST(ParserA87, DecimalDigitAll) {
  auto r = Parse("module m; int x; initial x = 1234567890; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 1234567890u);
}

// § binary_digit — 0 and 1
TEST(ParserA87, BinaryDigitZeroOne) {
  auto r = Parse("module m; logic [3:0] x; initial x = 4'b0101; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->int_val, 5u);
}

}  // namespace
