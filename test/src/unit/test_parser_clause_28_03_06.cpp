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

}  // namespace
