#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(AssocArrayPrevParsing, AssocArrayPrevMethodIntKey) {
  auto r = Parse(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  initial x = aa.prev(k);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(AssocArrayPrevParsing, AssocArrayPrevMethodStringKey) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  string s;\n"
      "  initial x = aa.prev(s);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(AssocArrayPrevParsing, AssocArrayPrevInIfCondition) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int aa[string];\n"
              "  string s;\n"
              "  initial if (aa.prev(s)) $display(s);\n"
              "endmodule\n"));
}

TEST(AssocArrayPrevParsing, AssocArrayPrevReturnAssigned) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int aa[int];\n"
              "  int k;\n"
              "  int status;\n"
              "  initial status = aa.prev(k);\n"
              "endmodule\n"));
}

}  // namespace
