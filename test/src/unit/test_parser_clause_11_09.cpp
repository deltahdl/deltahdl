#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

// tagged_union_expression ::= tagged member_identifier [ primary ]. The
// keyword introduces a kTagged node whose member identifier is the tag name
// and whose optional primary is the member value.
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

// For a void member the member value primary is omitted, so the kTagged node
// carries only the member identifier and no value subexpression.
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

// The optional-primary slot of the BNF accepts a bare literal: a kTagged node
// with the literal attached as its value subexpression should result.
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

// The optional-primary slot also accepts an assignment-pattern primary,
// e.g. tagged Add '{...}, producing a kTagged node whose value subexpression
// is the assignment pattern.
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

}  // namespace
