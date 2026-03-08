#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §7.9.4: first() parsed as method call on int-keyed associative array.
TEST(ParserSection7, AssocArrayFirstMethodIntKey) {
  auto r = Parse(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  initial x = aa.first(k);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

// §7.9.4: first() parsed as method call on string-keyed associative array.
TEST(ParserSection7, AssocArrayFirstMethodStringKey) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  string s;\n"
      "  initial x = aa.first(s);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

// §7.9.4: first() in if-condition context.
TEST(ParserSection7, AssocArrayFirstInIfCondition) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int aa[string];\n"
              "  string s;\n"
              "  initial if (aa.first(s)) $display(s);\n"
              "endmodule\n"));
}

// §7.9.4: first() return value used in assignment.
TEST(ParserSection7, AssocArrayFirstReturnAssigned) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int aa[int];\n"
              "  int k;\n"
              "  int status;\n"
              "  initial status = aa.first(k);\n"
              "endmodule\n"));
}

}  // namespace
