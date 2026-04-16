#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Scope resolution prefix produces correct AST structure ---

TEST(ScopeResolutionPrefixParsing, ExpressionPrefixTreeStructure) {
  auto r = Parse(
      "module t;\n"
      "  initial x = Pkg::val;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->lhs->text, "Pkg");
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->rhs->text, "val");
}

TEST(ScopeResolutionPrefixParsing, TypePrefixPopulatesScopeName) {
  auto r = Parse(
      "module t;\n"
      "  Scope::my_type x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kNamed);
  EXPECT_EQ(dt.scope_name, "Scope");
  EXPECT_EQ(dt.type_name, "my_type");
}

TEST(ScopeResolutionPrefixParsing, ChainedPrefixNestsCorrectly) {
  auto r = Parse(
      "module t;\n"
      "  initial x = A::B::c;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
  ASSERT_NE(rhs->lhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->lhs->text, "A");
  ASSERT_NE(rhs->lhs->rhs, nullptr);
  EXPECT_EQ(rhs->lhs->rhs->text, "B");
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->text, "c");
}

// --- Scope resolution prefix on assignment LHS ---

TEST(ScopeResolutionPrefixParsing, PrefixOnAssignmentLhs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial C::count = 5;\n"
              "endmodule\n"));
}

// --- Scope resolution prefix in subexpression ---

TEST(ScopeResolutionPrefixParsing, PrefixInBinaryExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial x = Pkg::A + Cls::B;\n"
              "endmodule\n"));
}

}  // namespace
