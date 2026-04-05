#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(StringLiteralVectorParsing, StringLiteralCopyToVector) {
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

TEST(StringLiteralVectorParsing, StringLiteralConcatInVector) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*14:1] stringvar;\n"
              "  initial begin\n"
              "    stringvar = \"Hello world\";\n"
              "    stringvar = {stringvar, \"!!!\"};\n"
              "  end\n"
              "endmodule\n"));
}

TEST(StringLiteralVectorParsing, StringLiteralCompare) {
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

TEST(StringLiteralVectorParsing, StringLiteralCaseEqualityParses) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*5:1] s1, s2;\n"
              "  logic result;\n"
              "  initial begin\n"
              "    s1 = \"Hello\";\n"
              "    s2 = \"Hello\";\n"
              "    result = (s1 === s2);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(StringLiteralVectorParsing, StringLiteralConcatOfPureLiterals) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*4:1] s;\n"
              "  initial s = {\"AB\", \"CD\"};\n"
              "endmodule\n"));
}

TEST(StringLiteralVectorParsing, StringLiteralToSmallerVector) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [15:0] s;\n"
              "  initial s = \"ABC\";\n"
              "endmodule\n"));
}

}  // namespace
