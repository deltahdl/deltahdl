#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PrimitiveTerminals, PassSwitchInoutLiteral) {
  auto r = Parse(
      "module m;\n"
      "  tran (1, b);\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "inout terminal must be a net lvalue", 2, "28.3"));
}

TEST(PrimitiveTerminals, PassEnSwitchInoutExpression) {
  auto r = Parse(
      "module m;\n"
      "  tranif0 (a + b, c, en);\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "inout terminal must be a net lvalue", 2, "28.3"));
}

TEST(PrimitiveTerminals, NInputGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  and (1, a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "output terminal must be a net lvalue", 2,
                            "28.3"));
}

TEST(PrimitiveTerminals, NOutputGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  buf (1, a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "output terminal must be a net lvalue", 2,
                            "28.3"));
}

TEST(PrimitiveTerminals, ThreeStateGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (1, a, en);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "output terminal must be a net lvalue", 2,
                            "28.3"));
}

TEST(PrimitiveTerminals, MosSwitchOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  nmos (1, a, en);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "output terminal must be a net lvalue", 2,
                            "28.3"));
}

TEST(PrimitiveTerminals, ConnectionListWithoutParenthesesRejected) {
  auto r = Parse(
      "module m;\n"
      "  and y, a, b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '(', got ','", 2, "28.3.6"));
}

TEST(PrimitiveTerminals, TerminalsWithoutSeparatingCommaRejected) {
  auto r = Parse(
      "module m;\n"
      "  and (y a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ')', got identifier", 2, "28.3.6"));
}

TEST(GateInstance, MalformedTerminalListNames28_3_6) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')'", 2, "28.3.6"));
}

}  // namespace
