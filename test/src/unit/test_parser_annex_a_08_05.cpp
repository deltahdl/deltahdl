// Annex A.8.5: Expression left-side values

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

static ModuleItem* FirstContAssign(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// A.8.5 Expression left-side values — net_lvalue
// =============================================================================
// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (simple net)
TEST(ParserA85, NetLvalueSimpleIdent) {
  auto r = Parse("module m; wire a, b; assign a = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ca->assign_lhs->text, "a");
}

// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (bit select)
TEST(ParserA85, NetLvalueConstBitSelect) {
  auto r =
      Parse("module m; wire [7:0] a; wire b; assign a[3] = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_lhs->base, nullptr);
  EXPECT_EQ(ca->assign_lhs->base->text, "a");
}

// § net_lvalue — ps_or_hierarchical_net_identifier constant_select (part
// select)
TEST(ParserA85, NetLvalueConstPartSelect) {
  auto r = Parse(
      "module m; wire [7:0] a; wire [3:0] b; assign a[7:4] = b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
  ASSERT_NE(ca->assign_lhs->index_end, nullptr);
}

// § net_lvalue — { net_lvalue { , net_lvalue } } (concatenation)
TEST(ParserA85, NetLvalueConcatenation) {
  auto r = Parse(
      "module m; wire [7:0] a; wire [3:0] b, c; assign {b, c} = a; "
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements.size(), 2u);
}

// § net_lvalue — nested concatenation
TEST(ParserA85, NetLvalueNestedConcatenation) {
  auto r = Parse(
      "module m; wire a, b, c, d;\n"
      "  assign {{a, b}, {c, d}} = 4'hF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements.size(), 2u);
  EXPECT_EQ(ca->assign_lhs->elements[0]->kind, ExprKind::kConcatenation);
}

// § net_lvalue — concatenation with selects
TEST(ParserA85, NetLvalueConcatWithSelects) {
  auto r = Parse(
      "module m; wire [7:0] a; wire [3:0] b;\n"
      "  assign {a[7:4], b} = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(ca->assign_lhs->elements[0]->kind, ExprKind::kSelect);
}

// =============================================================================
// A.8.5 Expression left-side values — variable_lvalue
// =============================================================================
// § variable_lvalue — hierarchical_variable_identifier (simple variable)
TEST(ParserA85, VarLvalueSimpleIdent) {
  auto r = Parse("module m; logic x; initial x = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "x");
}

}  // namespace
