#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §6.3.2.2: Drive strength (strength1, strength0) — reversed order.
TEST(ParserA222, DriveStrengthStr1Highz0) {
  auto r = Parse(
      "module m;\n"
      "  wire (strong1, highz0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1u);   // highz0
  EXPECT_EQ(item->drive_strength1, 4u);   // strong1
}

// §6.3.2.2: Drive strength (strength0, strength1) — normal order.
TEST(ParserA222, DriveStrengthStr0Str1) {
  auto r = Parse(
      "module m;\n"
      "  wire (strong0, pull1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 4u);   // strong0
  EXPECT_EQ(item->drive_strength1, 3u);   // pull1
}

// §6.3.2.2: Drive strength with supply0.
TEST(ParserA222, DriveStrengthSupply0Weak1) {
  auto r = Parse(
      "module m;\n"
      "  wire (supply0, weak1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 5u);   // supply0
  EXPECT_EQ(item->drive_strength1, 2u);   // weak1
}

// §6.3.2.2: Drive strength with supply1.
TEST(ParserA222, DriveStrengthPull0Supply1) {
  auto r = Parse(
      "module m;\n"
      "  wire (pull0, supply1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 3u);   // pull0
  EXPECT_EQ(item->drive_strength1, 5u);   // supply1
}

// §6.3.2.2: Drive strength weak0, weak1.
TEST(ParserA222, DriveStrengthWeak0Weak1) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, weak1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 2u);   // weak0
  EXPECT_EQ(item->drive_strength1, 2u);   // weak1
}

// §6.3.2.2: Drive strength highz0, strong1.
TEST(ParserA222, DriveStrengthHighz0Strong1) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz0, strong1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 1u);   // highz0
  EXPECT_EQ(item->drive_strength1, 4u);   // strong1
}

// §6.3.2.2: Drive strength supply0, supply1.
TEST(ParserA222, DriveStrengthSupply0Supply1) {
  auto r = Parse(
      "module m;\n"
      "  wire (supply0, supply1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 5u);   // supply0
  EXPECT_EQ(item->drive_strength1, 5u);   // supply1
}

// §6.3.2.2: Drive strength highz1, pull0 — reversed order.
TEST(ParserA222, DriveStrengthHighz1Pull0) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz1, pull0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 3u);   // pull0
  EXPECT_EQ(item->drive_strength1, 1u);   // highz1
}

// §6.3.2.2: Net declaration without drive strength has default (0, 0).
TEST(ParserA222, NetDeclNoDriveStrengthDefault) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 0u);
  EXPECT_EQ(item->drive_strength1, 0u);
}

// §6.3.2.2: Drive strength on continuous assignment.
TEST(ParserA222, ContinuousAssignDriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b1;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r, ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 4u);   // strong0
  EXPECT_EQ(item->drive_strength1, 2u);   // weak1
}

// §6.3.2.2: Drive strength (highz0, highz1) parses but is semantically illegal.
TEST(ParserA222, DriveStrengthHighz0Highz1_ParsesOk) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz0, highz1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 1u);
  EXPECT_EQ(item->drive_strength1, 1u);
}

// §6.3.2.2: Drive strength on tri net type.
TEST(ParserA222, DriveStrengthOnTri) {
  auto r = Parse(
      "module m;\n"
      "  tri (pull0, pull1) t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 3u);   // pull0
  EXPECT_EQ(item->drive_strength1, 3u);   // pull1
}

}  // namespace
