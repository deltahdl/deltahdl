

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PrimitiveTerminals, PassSwitchInoutLiteral) {
  auto r = Parse(
      "module m;\n"
      "  tran (1, b);\n"
      "endmodule\n");
  // §28.3 owns the report that a terminal must be a net lvalue; §28.3.6 states
  // the connection-list syntax and has no report of its own here.
  EXPECT_TRUE(
      ReportedError(r.diags, "inout terminal must be a net lvalue", 2, "28.3"));
}

TEST(PrimitiveTerminals, PassEnSwitchInoutExpression) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (a + b, c, en);\n"
      "endmodule\n");
  // §28.3 owns the net-lvalue report, not §28.3.6.
  EXPECT_TRUE(
      ReportedError(r.diags, "inout terminal must be a net lvalue", 2, "28.3"));
}

TEST(PrimitiveTerminals, NInputGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  and (1, a, b);\n"
      "endmodule\n");
  // §28.3 owns the net-lvalue report, not §28.3.6.
  EXPECT_TRUE(ReportedError(r.diags, "output terminal must be a net lvalue", 2,
                            "28.3"));
}

TEST(PrimitiveTerminals, NOutputGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  buf (1, a);\n"
      "endmodule\n");
  // §28.3 owns the net-lvalue report, not §28.3.6.
  EXPECT_TRUE(ReportedError(r.diags, "output terminal must be a net lvalue", 2,
                            "28.3"));
}

// §28.3.6: the output terminal comes first for a three-state gate too, so its
// leading terminal must be a drivable net; a literal in that position is
// rejected.
TEST(PrimitiveTerminals, ThreeStateGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (1, a, en);\n"
      "endmodule\n");
  // §28.3 owns the net-lvalue report, not §28.3.6.
  EXPECT_TRUE(ReportedError(r.diags, "output terminal must be a net lvalue", 2,
                            "28.3"));
}

// §28.3.6: a MOS switch also lists its output terminal first, so a literal in
// the leading position is rejected.
TEST(PrimitiveTerminals, MosSwitchOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  nmos (1, a, en);\n"
      "endmodule\n");
  // §28.3 owns the net-lvalue report, not §28.3.6.
  EXPECT_TRUE(ReportedError(r.diags, "output terminal must be a net lvalue", 2,
                            "28.3"));
}

// §28.3.6: the connection list shall be enclosed in a pair of parentheses.
// Omitting them leaves the terminals dangling and shall be rejected.
TEST(PrimitiveTerminals, ConnectionListWithoutParenthesesRejected) {
  auto r = Parse(
      "module m;\n"
      "  and y, a, b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got ','", 2, "28.3.6"));
}

// §28.3.6: the terminals shall be separated by commas. Two adjacent terminal
// expressions with no separating comma shall be rejected.
TEST(PrimitiveTerminals, TerminalsWithoutSeparatingCommaRejected) {
  auto r = Parse(
      "module m;\n"
      "  and (y a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got identifier", 2, "28.3.6"));
}

// §28.3.6 parenthesizes a primitive instance's connection list. A terminal list
// left open is rejected at the token standing where the ')' belongs, and the
// report names §28.3.6 rather than the token it wanted.
TEST(GateInstance, MalformedTerminalListNames28_3_6) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')'", 2, "28.3.6"));
}

}  // namespace
