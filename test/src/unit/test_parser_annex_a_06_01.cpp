#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(ContinuousAssignSyntaxParsing,
     ListOfNetAssignments_SharedStrengthAndDelay) {
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

TEST(NetAliasSyntaxParsing, NetAliasBasic) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->alias_nets.size(), 2u);
}

TEST(NetAliasSyntaxParsing, NetAliasThreeNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->alias_nets.size(), 3u);
}

TEST(NetAliasSyntaxParsing, NetAliasFourNets) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  alias a = b = c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->alias_nets.size(), 4u);
}

TEST(NetAliasSyntaxParsing, NetAliasMultipleStatements) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  alias a = b;\n"
      "  alias c = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  size_t count =
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kAlias);
  EXPECT_EQ(count, 2u);
}

TEST(ContinuousAssignSyntaxParsing, VariableContinuousAssignWithDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  logic x;\n"
      "  assign #5 x = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assign_delay, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, ListOfVariableAssignments_Two) {
  auto r = Parse(
      "module m;\n"
      "  logic x, y;\n"
      "  assign x = 1'b0, y = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 2u);
  EXPECT_EQ(cas[0]->assign_lhs->text, "x");
  EXPECT_EQ(cas[1]->assign_lhs->text, "y");
}

TEST(ContinuousAssignSyntaxParsing, ListOfVariableAssignments_Three) {
  auto r = Parse(
      "module m;\n"
      "  logic x, y, z;\n"
      "  assign x = 1'b0, y = 1'b1, z = 1'bx;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 3u);
}

TEST(NetAliasSyntaxParsing, NetAliasLvalueIsExpression) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] a, b;\n"
      "  alias a[1:0] = b[3:2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->alias_nets.size(), 2u);
}

TEST(NetAliasSyntaxParsing, NetAliasConcatLvalues) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] a, b;\n"
      "  wire [1:0] hi, lo;\n"
      "  alias {hi, lo} = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->alias_nets.size(), 2u);
  EXPECT_EQ(item->alias_nets[0]->kind, ExprKind::kConcatenation);
}

TEST(NetAliasSyntaxParsing, NetAliasBitSelectLvalue) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] a;\n"
      "  wire b;\n"
      "  alias a[0] = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kAlias);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->alias_nets.size(), 2u);
}

TEST(NetAliasSyntaxParsing, AliasSingleNetIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire a;\n"
      "  alias a;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(NetAliasSyntaxParsing, AliasMissingSemicolonIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ContinuousAssignSyntaxParsing, AssignMissingSemicolonIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ContinuousAssignSyntaxParsing, NetAssignmentMissingEqualsIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a b;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ContinuousAssignSyntaxParsing, NetAssignmentMissingRhsIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire a;\n"
      "  assign a = ;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ContinuousAssignSyntaxParsing, NetAssignmentBitSelectLvalue) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] a;\n"
      "  wire b;\n"
      "  assign a[0] = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_lhs, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, NetAssignmentPartSelectLvalue) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] a;\n"
      "  wire [3:0] b;\n"
      "  assign a[3:0] = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_lhs, nullptr);
}

TEST(ContinuousAssignSyntaxParsing, NetAssignmentLiteralRhs) {
  auto r = Parse(
      "module m;\n"
      "  wire [3:0] a;\n"
      "  assign a = 4'b1010;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->assign_rhs, nullptr);
}

}  // namespace
