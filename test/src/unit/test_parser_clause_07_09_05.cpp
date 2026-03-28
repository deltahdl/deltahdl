#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(AssocArrayLastParsing, AssocArrayLastMethodIntKey) {
  auto r = Parse(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  initial x = aa.last(k);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(AssocArrayLastParsing, AssocArrayLastMethodStringKey) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  string s;\n"
      "  initial x = aa.last(s);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(AssocArrayLastParsing, AssocArrayLastInIfCondition) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int aa[string];\n"
              "  string s;\n"
              "  initial if (aa.last(s)) $display(s);\n"
              "endmodule\n"));
}

TEST(AssocArrayLastParsing, AssocArrayLastReturnAssigned) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int aa[int];\n"
              "  int k;\n"
              "  int status;\n"
              "  initial status = aa.last(k);\n"
              "endmodule\n"));
}

}  // namespace
