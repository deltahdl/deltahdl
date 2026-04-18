// §28.3.6

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Net lvalue validation on output/inout terminals ---
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

TEST(PrimitiveTerminals, EnableGateOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (1, a, en);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveTerminals, MosSwitchOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  nmos (1, a, g);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveTerminals, CmosSwitchOutputLiteralRejected) {
  auto r = Parse(
      "module m;\n"
      "  cmos (1, a, n, p);\n"
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

}  // namespace
