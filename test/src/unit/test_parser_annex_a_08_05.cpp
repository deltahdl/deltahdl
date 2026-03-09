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

TEST(ParserA85, VarLvalueBitSelect) {
  auto r = Parse("module m; logic [7:0] x; initial x[3] = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->lhs->base, nullptr);
  EXPECT_EQ(stmt->lhs->base->text, "x");
  ASSERT_NE(stmt->lhs->index, nullptr);
  EXPECT_EQ(stmt->lhs->index_end, nullptr);
}

TEST(ParserA85, VarLvaluePartSelect) {
  auto r = Parse("module m; logic [7:0] x; initial x[7:4] = 4'hF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(stmt->lhs->index, nullptr);
  ASSERT_NE(stmt->lhs->index_end, nullptr);
}

TEST(ParserA85, VarLvalueIndexedPartSelectPlus) {
  auto r =
      Parse("module m; logic [15:0] x; initial x[4+:4] = 4'hF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->lhs->is_part_select_plus);
}

TEST(ParserA85, VarLvalueIndexedPartSelectMinus) {
  auto r =
      Parse("module m; logic [15:0] x; initial x[7-:4] = 4'hF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->lhs->is_part_select_minus);
}

TEST(ParserA85, VarLvalueMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p.hi = 8'hAB;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserA85, VarLvalueConcatenation) {
  auto r = Parse(
      "module m; logic [3:0] a, b; logic [7:0] c;\n"
      "  initial {a, b} = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements.size(), 2u);
}

TEST(ParserA85, VarLvalueNestedConcatenation) {
  auto r = Parse(
      "module m; logic a, b, c, d;\n"
      "  initial {{a, b}, {c, d}} = 4'hF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->lhs->elements[0]->kind, ExprKind::kConcatenation);
}

TEST(ParserA85, VarLvalueStreamingConcat) {
  auto r = Parse(
      "module m; logic [31:0] a, b;\n"
      "  initial {>> {a}} = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kStreamingConcat);
}

TEST(ParserA85, NonrangeVarLvalueSimple) {
  auto r = Parse("module m; int x; initial x = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->lhs->text, "x");
}

TEST(ParserA85, NonrangeVarLvalueMemberAccess) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } s_t;\n"
      "  s_t s;\n"
      "  initial s.a = 8'h12;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kMemberAccess);
}

}
