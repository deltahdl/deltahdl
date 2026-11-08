#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(FormalSyntaxParsing, MemberAccess) {
  auto r = Parse("module m; initial x = s.field; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(FormalSyntaxParsing, ChainedMemberAccess) {
  auto r = Parse("module m; initial x = u.Add.reg1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(TaggedUnionExprParsing, TaggedWithMemberValue) {
  auto r = Parse("module m; initial x = tagged Valid (23 + 34); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Valid");
  EXPECT_NE(rhs->lhs, nullptr);
}

TEST(TaggedUnionExprParsing, TaggedVoidMemberOmitsValue) {
  auto r = Parse("module m; initial x = tagged Invalid; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Invalid");
  EXPECT_EQ(rhs->lhs, nullptr);
}

TEST(TaggedUnionExprParsing, TaggedWithBareLiteralPrimary) {
  auto r = Parse("module m; initial x = tagged Valid 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Valid");
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIntegerLiteral);
}

TEST(TaggedUnionExprParsing, TaggedWithAssignmentPatternPrimary) {
  auto r = Parse("module m; initial x = tagged Add '{19, 4, 3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Add");
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kAssignmentPattern);
}

TEST(TaggedUnionExprParsing, TaggedWithoutMemberIdentifierRejected) {
  auto r = Parse("module m; initial x = tagged 42; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got integer literal",
                            1, "7.3.2"));
}

}  // namespace
