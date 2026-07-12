#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §7.9.2 prototype `function void delete( [input index] )` with the optional
// index supplied: it parses as a call carrying exactly one argument (the
// index), distinguishing it from the no-argument form below.
TEST(AggregateTypeParsing, AssocArrayDeleteMethodWithIndex) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete(\"key\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kCall);
  EXPECT_EQ(stmt->expr->args.size(), 1u);
}

// §7.9.2 prototype with the index omitted: it parses as a call carrying no
// arguments, observing that the index is optional.
TEST(AggregateTypeParsing, AssocArrayDeleteMethodNoArg) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kCall);
  EXPECT_TRUE(stmt->expr->args.empty());
}

// The parenless delete-all form parses as a bare member access (no call
// parentheses), the third accepted spelling of the §7.9.2 prototype.
TEST(AggregateTypeParsing, AssocArrayDeletePropertySyntax) {
  auto r = Parse(
      "module t;\n"
      "  int aa[string];\n"
      "  initial aa.delete;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
}

}  // namespace
