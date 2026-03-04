#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection11, StringLiteralToVector) {
  auto r = Parse(
      "module t;\n"
      "  bit [8*14:1] stringvar;\n"
      "  initial stringvar = \"Hello world\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(ParserSection11, StringConcatToVector) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*14:1] stringvar;\n"
              "  initial begin\n"
              "    stringvar = \"Hello world\";\n"
              "    stringvar = {stringvar, \"!!!\"};\n"
              "  end\n"
              "endmodule\n"));
}

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
