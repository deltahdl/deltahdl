#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(NetDeclDriveStrengthParsing, StrengthAndAssignmentReachOneDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  wire (pull1, weak0) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->drive_strength0, 2);
  EXPECT_EQ(item->drive_strength1, 3);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(NetDeclDriveStrengthParsing, StrengthKeywordsMayBeWrittenInEitherOrder) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, pull1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 2);
  EXPECT_EQ(item->drive_strength1, 3);
}

TEST(NetDeclDriveStrengthParsing, DeclarationWithNoStrengthLeavesBothUnset) {
  auto r = Parse(
      "module m;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 0);
  EXPECT_EQ(item->drive_strength1, 0);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(NetDeclDriveStrengthParsing, StrengthHeadsAListOfSeparateDeclarators) {
  auto r = Parse(
      "module m;\n"
      "  wire (pull1, weak0) a = 1'b1, b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[1]->drive_strength0, 2);
  EXPECT_EQ(items[1]->drive_strength1, 3);
  EXPECT_NE(items[0]->init_expr, nullptr);
  EXPECT_EQ(items[1]->init_expr, nullptr);
}

TEST(NetDeclDriveStrengthParsing, TriregCarriesAStrengthWithItsAssignment) {
  auto r = Parse(
      "module m;\n"
      "  trireg (pull1, weak0) t = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->drive_strength0, 2);
  EXPECT_EQ(item->drive_strength1, 3);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(NetDeclDriveStrengthParsing, TriregStrengthPrecedesItsDelay) {
  auto r = Parse(
      "module m;\n"
      "  trireg (pull1, weak0) #5 t = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 2);
  EXPECT_EQ(item->drive_strength1, 3);
  EXPECT_NE(item->net_delay, nullptr);
}

}  // namespace
