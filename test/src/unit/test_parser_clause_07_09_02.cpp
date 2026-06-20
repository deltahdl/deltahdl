#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(AggregateTypeParsing, AssocArrayDeleteMethodWithIndex) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete(\"key\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(AggregateTypeParsing, AssocArrayDeleteMethodNoArg) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(AggregateTypeParsing, AssocArrayDeletePropertySyntax) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
}

}  // namespace
