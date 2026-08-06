

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PrimitiveTerminals, PassSwitchInoutLiteral) {
  auto r = Parse(
      "module m;\n"
      "  tran (1, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveTerminals, PassEnSwitchInoutExpression) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (a + b, c, en);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveTerminals, NInputGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  and (1, a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveTerminals, NOutputGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  buf (1, a);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §28.3.6: the output terminal comes first for a three-state gate too, so its
// leading terminal must be a drivable net; a literal in that position is
// rejected.
TEST(PrimitiveTerminals, ThreeStateGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (1, a, en);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §28.3.6: a MOS switch also lists its output terminal first, so a literal in
// the leading position is rejected.
TEST(PrimitiveTerminals, MosSwitchOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  nmos (1, a, en);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §28.3.6: the connection list shall be enclosed in a pair of parentheses.
// Omitting them leaves the terminals dangling and shall be rejected.
TEST(PrimitiveTerminals, ConnectionListWithoutParenthesesRejected) {
  auto r = Parse(
      "module m;\n"
      "  and y, a, b;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §28.3.6: the terminals shall be separated by commas. Two adjacent terminal
// expressions with no separating comma shall be rejected.
TEST(PrimitiveTerminals, TerminalsWithoutSeparatingCommaRejected) {
  auto r = Parse(
      "module m;\n"
      "  and (y a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
