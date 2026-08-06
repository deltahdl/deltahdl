#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(AssocArrayNextParsing, AssocArrayNextMethodIntKey) {
  auto r = Parse(
      "module t;\n"
      "  int aa[int];\n"
      "  int k;\n"
      "  initial x = aa.next(k);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(AssocArrayNextParsing, AssocArrayNextMethodStringKey) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  string s;\n"
      "  initial x = aa.next(s);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(AssocArrayNextParsing, AssocArrayNextInIfCondition) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int aa[string];\n"
              "  string s;\n"
              "  initial if (aa.next(s)) $display(s);\n"
              "endmodule\n"));
}

// The clause 7.9.6 worked example drives next() as the controlling expression
// of a do/while loop, so parsing must accept a next() call in that condition
// position -- distinct from the if-condition and assignment-RHS positions
// above.
TEST(AssocArrayNextParsing, AssocArrayNextInDoWhileCondition) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int aa[string];\n"
              "  string s;\n"
              "  initial begin\n"
              "    if (aa.first(s))\n"
              "      do $display(s); while (aa.next(s));\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
