

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StrengthParsing, DriveStrengthHighz0Highz1ParsesWithoutError) {
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

TEST(StrengthParsing, DriveStrengthOnTri) {
  auto r = Parse(
      "module m;\n"
      "  tri (pull0, pull1) t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 3u);
  EXPECT_EQ(item->drive_strength1, 3u);
}

TEST(StrengthParsing, DriveStrengthWithAssignment) {
  auto r = Parse(
      "module m;\n"
      "  wire (strong0, pull1) w = 1'b1;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 3u);
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(StrengthParsing, NoStrengthNoFields) {
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

}
