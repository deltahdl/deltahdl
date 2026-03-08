#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection11, Sec11_1_StringLiteralAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  string s;\n"
      "  initial s = \"hello world\";\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

}
