#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "simulator/udp_eval.h"

using namespace delta;
namespace {

TEST(ParserA601, ContinuousAssign_Basic) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  ASSERT_NE(cas[0]->assign_lhs, nullptr);
  ASSERT_NE(cas[0]->assign_rhs, nullptr);
}

TEST(ParserA601, ListOfNetAssignments_Two) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 2u);
  EXPECT_EQ(cas[0]->assign_lhs->text, "a");
  EXPECT_EQ(cas[1]->assign_lhs->text, "c");
}

TEST(ParserA601, ListOfNetAssignments_Three) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d, e, f;\n"
      "  assign a = b, c = d, e = f;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 3u);
  EXPECT_EQ(cas[0]->assign_lhs->text, "a");
  EXPECT_EQ(cas[1]->assign_lhs->text, "c");
  EXPECT_EQ(cas[2]->assign_lhs->text, "e");
}

TEST(ParserA601, ListOfNetAssignments_SharedStrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign (strong0, strong1) #10 a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 2u);
  EXPECT_EQ(cas[0]->drive_strength0, 4u);
  EXPECT_EQ(cas[1]->drive_strength0, 4u);
  EXPECT_EQ(cas[0]->drive_strength1, 4u);
  EXPECT_EQ(cas[1]->drive_strength1, 4u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_NE(cas[1]->assign_delay, nullptr);
}

TEST(ParserA601, NetAssignment_ConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] sum;\n"
      "  wire carry;\n"
      "  assign {carry, sum} = 5'b10101;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->assign_lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserA601, NetAssignment_ExprRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] a, b, sum;\n"
      "  assign sum = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->assign_rhs->kind, ExprKind::kBinary);
}
TEST(ParserSection6, VariableContinuousAssign) {
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

TEST(ParserSection10, ContinuousAssignMultipleTargets) {
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

TEST(ParserSection4, Sec4_5_ContinuousAssign) {
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

TEST(ParserSection6, RealVariableContinuousAssign) {
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

TEST(ParserSection10, ContinuousAssignExpression) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] a, b, sum;\n"
      "  assign sum = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* ca =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_rhs, nullptr);
  EXPECT_EQ(ca->assign_rhs->kind, ExprKind::kBinary);
}

TEST(ParserSection10, ContinuousAssignTernary) {
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

TEST(ParserSection6, Sec6_5_NetDrivenByContAssign) {
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

TEST(ParserSection6, Sec6_5_VarWithContAssign) {
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

TEST(ParserA82, TfCallInContAssign) {
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

TEST(ParserA83, ExprInContAssign) {
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

TEST(ParserSection11, Sec11_4_1_BitSelectInContAssignLhs) {
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

TEST(ParserSection7, Sec7_2_1_PackedContAssign) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] a;\n"
              "    logic [7:0] b;\n"
              "  } pair_t;\n"
              "  pair_t p;\n"
              "  assign p = 16'h1234;\n"
              "endmodule\n"));
}
static ModuleItem* NthItem(ParseResult& r, size_t n) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.size() <= n)
    return nullptr;
  return r.cu->modules[0]->items[n];
}

TEST(ParserSection7, Sec7_2_2_ContinuousAssign) {
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
