#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ContAssignStatementParsing, VariableContinuousAssign) {
  auto r = Parse(
      "module t;\n"
      "  logic vw;\n"
      "  assign vw = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  bool found_ca = false;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kContAssign) found_ca = true;
  }
  EXPECT_TRUE(found_ca);
}

TEST(ContAssignStatementParsing, ContinuousAssignMultipleTargets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  int count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kContAssign) count++;
  }
  EXPECT_GE(count, 1);
}
static ModuleItem* FindItemByKindFromResult(ParseResult& r,
                                            ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static ModuleItem* FindContAssign(ParseResult& r) {
  return FindItemByKindFromResult(r, ModuleItemKind::kContAssign);
}

TEST(ContAssignStatementParsing, WireWithBinaryExpression) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  wire a, b;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindContAssign(r);
  ASSERT_NE(ca, nullptr);
  EXPECT_NE(ca->assign_lhs, nullptr);
  EXPECT_NE(ca->assign_rhs, nullptr);
}

TEST(ContAssignStatementParsing, RealVariableContinuousAssign) {
  auto r = Parse(
      "module t;\n"
      "  real circ;\n"
      "  assign circ = 2.0 * 3.14;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  bool found_ca = false;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kContAssign) found_ca = true;
  }
  EXPECT_TRUE(found_ca);
}

TEST(ContAssignStatementParsing, ContinuousAssignTernary) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, sel, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ca =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
}

TEST(ContAssignStatementParsing, NetDrivenByContAssign) {
  auto r = Parse(
      "module t;\n"
      "  wire out;\n"
      "  assign out = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kContAssign);
  ASSERT_NE(items[1]->assign_lhs, nullptr);
  ASSERT_NE(items[1]->assign_rhs, nullptr);
}

TEST(ContAssignStatementParsing, VarWithContAssign) {
  auto r = Parse(
      "module t;\n"
      "  logic y;\n"
      "  assign y = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kContAssign);
}

static Expr* FirstContAssignRHS(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item->assign_rhs;
  }
  return nullptr;
}

TEST(ContAssignStatementParsing, FunctionCallInRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  function logic [7:0] compute(input logic [7:0] a);\n"
      "    return a + 8'd1;\n"
      "  endfunction\n"
      "  assign y = compute(8'd5);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstContAssignRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
  EXPECT_EQ(rhs->callee, "compute");
}

TEST(ContAssignStatementParsing, BinaryExprInRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  wire [7:0] a, b;\n"
      "  assign y = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstContAssignRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}
static ModuleItem* FirstContAssign(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) return item;
  }
  return nullptr;
}

TEST(ContAssignStatementParsing, BitSelectInContAssignLhs) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] vec;\n"
      "  wire val;\n"
      "  assign vec[0] = val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FirstContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_lhs, nullptr);
  EXPECT_EQ(ca->assign_lhs->kind, ExprKind::kSelect);
  EXPECT_EQ(ca->assign_lhs->index_end, nullptr);
}

static ModuleItem* NthItem(ParseResult& r, size_t n) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.size() <= n)
    return nullptr;
  return r.cu->modules[0]->items[n];
}

TEST(ContAssignStatementParsing, PackedStructAssign) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } s_t;\n"
      "  s_t s;\n"
      "  assign s = 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = NthItem(r, 2);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  ASSERT_NE(item->assign_lhs, nullptr);
  ASSERT_NE(item->assign_rhs, nullptr);
}

}  // namespace
