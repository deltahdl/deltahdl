#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(EmptyStringLiteralParsing, EmptyStringLiteralParses) {
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

TEST(EmptyStringLiteralParsing, EmptyStringComparedWithZeroParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic result;\n"
              "  initial result = (\"\" == \"0\");\n"
              "endmodule\n"));
}

TEST(EmptyStringLiteralParsing, EmptyStringComparedWithNulEscapeParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic result;\n"
              "  initial result = (\"\" == \"\\0\");\n"
              "endmodule\n"));
}

TEST(EmptyStringLiteralParsing, EmptyStringInConditionalParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic r;\n"
              "  initial if (\"\") r = 1;\n"
              "endmodule\n"));
}

}  // namespace
