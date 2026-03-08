#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §11.10.1: Copy — string literal assigned to a vector via simple assignment.
TEST(ParserSection1110_1, StringLiteralCopyToVector) {
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

// §11.10.1: Concatenate — string literals concatenated via concatenation operator.
TEST(ParserSection1110_1, StringLiteralConcatInVector) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*14:1] stringvar;\n"
              "  initial begin\n"
              "    stringvar = \"Hello world\";\n"
              "    stringvar = {stringvar, \"!!!\"};\n"
              "  end\n"
              "endmodule\n"));
}

// §11.10.1: Compare — string literal values compared with equality operators.
TEST(ParserSection1110_1, StringLiteralCompare) {
  auto r = Parse(
      "module t;\n"
      "  bit [8*10:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \"Hello\";\n"
      "    result = (s1 == s2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §11.10.1: Vectors should be at least 8*n bits to preserve ASCII encoding.
TEST(ParserSection1110_1, StringLiteralWideVector) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*20:1] wide;\n"
              "  initial wide = \"short\";\n"
              "endmodule\n"));
}

}  // namespace
