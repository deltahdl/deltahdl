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

}  // namespace
