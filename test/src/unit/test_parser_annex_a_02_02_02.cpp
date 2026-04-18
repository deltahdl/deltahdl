#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(StrengthParsing, DriveStrengthStr0Str1) {
  auto r = Parse(
      "module m;\n"
      "  wire (strong0, weak1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 2u);
}

TEST(StrengthParsing, DriveStrengthStr1Str0) {
  auto r = Parse(
      "module m;\n"
      "  wire (pull1, supply0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 5u);
  EXPECT_EQ(item->drive_strength1, 3u);
}

TEST(StrengthParsing, DriveStrengthStr0Highz1) {
  auto r = Parse(
      "module m;\n"
      "  wire (pull0, highz1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 3u);
  EXPECT_EQ(item->drive_strength1, 1u);
}

TEST(StrengthParsing, DriveStrengthHighz0Str1) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz0, supply1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1u);
  EXPECT_EQ(item->drive_strength1, 5u);
}

TEST(StrengthParsing, DriveStrengthHighz1Str0) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz1, weak0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 2u);
  EXPECT_EQ(item->drive_strength1, 1u);
}

TEST(StrengthParsing, Strength0AllKeywords) {
  const struct {
    const char* keyword;
    uint8_t expected;
  } kCases[] = {
      {"supply0", 5},
      {"strong0", 4},
      {"pull0", 3},
      {"weak0", 2},
  };
  for (const auto& c : kCases) {
    auto src = std::string("module m;\n  wire (") + c.keyword +
               ", strong1) w;\nendmodule";
    auto r = Parse(src);
    ASSERT_NE(r.cu, nullptr) << "Failed for " << c.keyword;
    EXPECT_FALSE(r.has_errors) << "Failed for " << c.keyword;
    auto* item = r.cu->modules[0]->items[0];
    EXPECT_EQ(item->drive_strength0, c.expected) << "Failed for " << c.keyword;
  }
}

TEST(StrengthParsing, Strength1AllKeywords) {
  const struct {
    const char* keyword;
    uint8_t expected;
  } kCases[] = {
      {"supply1", 5},
      {"strong1", 4},
      {"pull1", 3},
      {"weak1", 2},
  };
  for (const auto& c : kCases) {
    auto src = std::string("module m;\n  wire (strong0, ") + c.keyword +
               ") w;\nendmodule";
    auto r = Parse(src);
    ASSERT_NE(r.cu, nullptr) << "Failed for " << c.keyword;
    EXPECT_FALSE(r.has_errors) << "Failed for " << c.keyword;
    auto* item = r.cu->modules[0]->items[0];
    EXPECT_EQ(item->drive_strength1, c.expected) << "Failed for " << c.keyword;
  }
}

TEST(StrengthParsing, StrengthValueEncoding) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, pull1) w1;\n"
      "  wire (supply0, supply1) w2;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* w1 = r.cu->modules[0]->items[0];
  EXPECT_EQ(w1->drive_strength0, 2u);
  EXPECT_EQ(w1->drive_strength1, 3u);
  auto* w2 = r.cu->modules[0]->items[1];
  EXPECT_EQ(w2->drive_strength0, 5u);
  EXPECT_EQ(w2->drive_strength1, 5u);
}

TEST(StrengthParsing, DriveStrengthStr1Highz0) {
  auto r = Parse(
      "module m;\n"
      "  wire (strong1, highz0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(StrengthParsing, NoDriveStrengthDefault) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 0u);
  EXPECT_EQ(item->drive_strength1, 0u);
}

TEST(StrengthParsing, AllDriveStrengthForms) {
  // Form 1: (strength0, strength1)
  auto r1 = Parse("module m; wire (weak0, pull1) w; endmodule");
  EXPECT_FALSE(r1.has_errors);
  // Form 2: (strength1, strength0)
  auto r2 = Parse("module m; wire (pull1, weak0) w; endmodule");
  EXPECT_FALSE(r2.has_errors);
  // Form 3: (strength0, highz1)
  auto r3 = Parse("module m; wire (supply0, highz1) w; endmodule");
  EXPECT_FALSE(r3.has_errors);
  // Form 4: (strength1, highz0)
  auto r4 = Parse("module m; wire (supply1, highz0) w; endmodule");
  EXPECT_FALSE(r4.has_errors);
  // Form 5: (highz0, strength1)
  auto r5 = Parse("module m; wire (highz0, weak1) w; endmodule");
  EXPECT_FALSE(r5.has_errors);
  // Form 6: (highz1, strength0)
  auto r6 = Parse("module m; wire (highz1, pull0) w; endmodule");
  EXPECT_FALSE(r6.has_errors);
}

}  // namespace
