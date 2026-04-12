#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DriveStrengthParsing, DriveStrengthContinuousAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, pull1) w = 1'b1;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 3u);
}
TEST(DriveStrengthParsing, ContinuousAssignStrengthEncoding) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 4u);
  EXPECT_EQ(cas[0]->drive_strength1, 2u);
}

TEST(DriveStrengthParsing, ContinuousAssignReversedStrengthOrder) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull1, supply0) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 5u);
  EXPECT_EQ(cas[0]->drive_strength1, 3u);
}

TEST(DriveStrengthParsing, ContinuousAssignStrengthWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign (pull0, pull1) #5 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->drive_strength0, 0u);
  EXPECT_NE(cas[0]->drive_strength1, 0u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
}

TEST(DriveStrengthParsing, NetDeclDriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, strong1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);

  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(DriveStrengthParsing, NetDeclAssignmentWithDriveStrength) {
  auto r = Parse("module m; wire (strong1, pull0) mynet = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "mynet");
  EXPECT_NE(item->init_expr, nullptr);
  EXPECT_NE(item->data_type.drive_strength0, 0);
  EXPECT_NE(item->data_type.drive_strength1, 0);
}

TEST(DriveStrengthParsing, ContinuousAssignWithDriveStrength) {
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

TEST(DriveStrengthParsing, ContinuousAssignStrengthAndDelay) {
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

TEST(DriveStrengthParsing, Supply0KeywordEncodesCorrectly) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (supply0, strong1) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 5u);
  EXPECT_EQ(cas[0]->drive_strength1, 4u);
}

TEST(DriveStrengthParsing, Supply1KeywordEncodesCorrectly) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, supply1) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 4u);
  EXPECT_EQ(cas[0]->drive_strength1, 5u);
}

TEST(DriveStrengthParsing, Highz0KeywordEncodesCorrectly) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, strong1) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 1u);
  EXPECT_EQ(cas[0]->drive_strength1, 4u);
}

TEST(DriveStrengthParsing, Highz1KeywordEncodesCorrectly) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, highz1) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 4u);
  EXPECT_EQ(cas[0]->drive_strength1, 1u);
}

TEST(DriveStrengthParsing, Highz0Highz1PairParsesWithoutError) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 1u);
  EXPECT_EQ(cas[0]->drive_strength1, 1u);
}

TEST(DriveStrengthParsing, NoStrengthEncodesAsZero) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 0u);
  EXPECT_EQ(cas[0]->drive_strength1, 0u);
}

TEST(DriveStrengthParsing, NetDeclReversedStrengthOrder) {
  auto r = Parse(
      "module m;\n"
      "  wire (strong1, weak0) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

}  // namespace
