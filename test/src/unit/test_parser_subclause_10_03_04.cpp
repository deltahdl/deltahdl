#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

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

TEST(DriveStrengthParsing, TwoStrength0KeywordsIsError) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak0) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "drive_strength on a continuous assignment requires one strength0", 3,
      "10.3.4"));
}

TEST(DriveStrengthParsing, TwoStrength1KeywordsIsError) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong1, pull1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags,
      "drive_strength on a continuous assignment requires one strength0", 3,
      "10.3.4"));
}

TEST(DriveStrengthParsing, NetDeclStrengthBeforeDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire (strong1, strong0) #5 w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 4u);
  EXPECT_NE(item->net_delay, nullptr);
}

TEST(DriveStrengthParsing, StrengthAfterDelayIsError) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #5 (pull0, pull1) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "the drive strength comes after the delay here; it "
                            "has to be written first",
                            3, "10.3.4"));
}

TEST(DriveStrengthParsing, NetDeclDelayBeforeStrengthIsError) {
  auto r = Parse(
      "module m;\n"
      "  wire #5 (strong1, strong0) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "the drive strength comes after the delay here; it "
                            "has to be written first",
                            2, "10.3.4"));
}

}  // namespace
