#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Integration robustness: in expression context the :: prefix builds a member
// access whose lhs/rhs are the prefix and member identifiers — the shape the
// elaborator inspects when applying §23.7.1.
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

// Integration robustness: in type context the :: prefix populates scope_name
// and type_name on the DataType — the fields the elaborator resolves per
// §23.7.1.
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

}  // namespace
