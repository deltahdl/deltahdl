#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §11.10.3: Empty string literal parses as string literal expression.
TEST(ParserSection1110_3, EmptyStringLiteralParses) {
  auto r = Parse(
      "module t;\n"
      "  bit [7:0] v;\n"
      "  initial v = \"\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

// §11.10.3: Empty string compared with "0" parses.
TEST(ParserSection1110_3, EmptyStringComparedWithZeroParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic result;\n"
              "  initial result = (\"\" == \"0\");\n"
              "endmodule\n"));
}

}  // namespace
