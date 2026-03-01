// §11.9: Tagged union expressions and member access

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A8MemberAccess) {
  auto r = Parse("module m; initial x = s.field; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

// §12.6: tagged expression — AST kind is kTagged
TEST(ParserA60701, TaggedExprAstKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = tagged Valid 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  // member identifier stored in rhs->rhs
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Valid");
}

// =============================================================================
// A.8.3 Expressions — tagged_union_expression
// =============================================================================
// § tagged_union_expression ::= tagged member_identifier [ primary ]
TEST(ParserA83, TaggedUnionWithValue) {
  auto r = Parse("module m; initial x = tagged Valid 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTagged);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "Valid");
  ASSERT_NE(rhs->lhs, nullptr);
}

TEST(ParserA83, TaggedUnionWithoutValue) {
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

}  // namespace
