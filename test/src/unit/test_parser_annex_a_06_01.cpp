#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ContinuousAssignSyntaxParsing, ContinuousAssignBasic) {
  auto r = Parse(
      "module m;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assign_lhs, nullptr);
  EXPECT_NE(item->assign_rhs, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, ContinuousAssignWithDriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  assign (strong1, weak0) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->drive_strength0, 0);
  EXPECT_NE(item->drive_strength1, 0);
}

TEST(ContinuousAssignSyntaxParsing, ContinuousAssignWithDelay3) {
  auto r = Parse(
      "module m;\n"
      "  assign #5 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assign_delay, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, ContinuousAssignWithDelay3TwoValues) {
  auto r = Parse(
      "module m;\n"
      "  assign #(5, 10) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assign_delay, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, ContinuousAssignWithDelay3ThreeValues) {
  auto r = Parse(
      "module m;\n"
      "  assign #(5, 10, 15) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assign_delay, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, ContinuousAssignStrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  assign (strong1, pull0) #10 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->drive_strength0, 0);
  EXPECT_NE(item->assign_delay, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, ListOfNetAssignments) {
  auto r = Parse(
      "module m;\n"
      "  assign a = b, c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) count++;
  }
  EXPECT_GE(count, 2);
}

TEST(ContinuousAssignSyntaxParsing, NetAliasTwoNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 2u);
}

TEST(ContinuousAssignSyntaxParsing, NetAliasThreeNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 3u);
}

TEST(ContinuousAssignSyntaxParsing, NetAssignmentWithExpression) {
  auto r = Parse(
      "module m;\n"
      "  assign y = a & b | c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assign_rhs, nullptr);
  EXPECT_EQ(item->assign_rhs->kind, ExprKind::kBinary);
}

TEST(ContinuousAssignSyntaxParsing, ContinuousAssignConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  assign {a, b} = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->assign_lhs->kind, ExprKind::kConcatenation);
}

TEST(ContinuousAssignSyntaxParsing, ContinuousAssign_Basic) {
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

TEST(ContinuousAssignSyntaxParsing, ListOfNetAssignments_Two) {
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

TEST(ContinuousAssignSyntaxParsing, ListOfNetAssignments_Three) {
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

TEST(ContinuousAssignSyntaxParsing, ListOfNetAssignments_SharedStrengthAndDelay) {
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

TEST(ContinuousAssignSyntaxParsing, NetAssignment_ConcatLhs) {
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

TEST(ContinuousAssignSyntaxParsing, NetAssignment_ExprRhs) {
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

TEST(ContinuousAssignSyntaxParsing, NetAlias_FourNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  alias a = b = c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 4u);
}

TEST(ContinuousAssignSyntaxParsing, NetAlias_BitSelect) {
  auto r = Parse(
      "module m;\n"
      "  wire [31:0] A, B;\n"
      "  alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* alias = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(alias, nullptr);
  ASSERT_EQ(alias->alias_nets.size(), 2u);
}

TEST(ContinuousAssignSyntaxParsing, VariableContinuousAssign) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assign_lhs, nullptr);
  EXPECT_NE(item->assign_rhs, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, NoDelayNoStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->assign_delay, nullptr);
  EXPECT_EQ(cas[0]->assign_delay_fall, nullptr);
  EXPECT_EQ(cas[0]->assign_delay_decay, nullptr);
  EXPECT_EQ(cas[0]->drive_strength0, 0u);
  EXPECT_EQ(cas[0]->drive_strength1, 0u);
}

TEST(ContinuousAssignSyntaxParsing, SingleNetAssignmentInList) {
  auto r = Parse(
      "module m;\n"
      "  wire x;\n"
      "  assign x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
}

TEST(ContinuousAssignSyntaxParsing, DelayFallAndDecayFields) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(3, 5, 7) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
  EXPECT_NE(cas[0]->assign_delay_fall, nullptr);
  EXPECT_NE(cas[0]->assign_delay_decay, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, MultipleAssignStatementsIndependent) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign a = b;\n"
      "  assign c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 2u);
}

TEST(ContinuousAssignment, SimpleNetAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_assign = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) has_assign = true;
  }
  EXPECT_TRUE(has_assign);
}

}  // namespace
