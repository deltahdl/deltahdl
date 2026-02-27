// Annex A.2.2.2: Strengths

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.2.2.2 Strengths
// =============================================================================
// --- drive_strength ---
// ( strength0 , strength1 ) | ( strength1 , strength0 )
// | ( strength0 , highz1 ) | ( strength1 , highz0 )
// | ( highz0 , strength1 ) | ( highz1 , strength0 )
TEST(ParserA222, DriveStrengthStr0Str1) {
  // ( strength0 , strength1 ): (strong0, weak1)
  auto r = Parse(
      "module m;\n"
      "  wire (strong0, weak1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 4u);  // strong0 = 4
  EXPECT_EQ(item->drive_strength1, 2u);  // weak1 = 2
}

TEST(ParserA222, DriveStrengthStr1Str0) {
  // ( strength1 , strength0 ): (pull1, supply0)
  auto r = Parse(
      "module m;\n"
      "  wire (pull1, supply0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 5u);  // supply0 = 5
  EXPECT_EQ(item->drive_strength1, 3u);  // pull1 = 3
}

TEST(ParserA222, DriveStrengthStr0Highz1) {
  // ( strength0 , highz1 ): (pull0, highz1)
  auto r = Parse(
      "module m;\n"
      "  wire (pull0, highz1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 3u);  // pull0 = 3
  EXPECT_EQ(item->drive_strength1, 1u);  // highz1 = 1
}

TEST(ParserA222, DriveStrengthHighz0Str1) {
  // ( highz0 , strength1 ): (highz0, supply1)
  auto r = Parse(
      "module m;\n"
      "  wire (highz0, supply1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1u);  // highz0 = 1
  EXPECT_EQ(item->drive_strength1, 5u);  // supply1 = 5
}

TEST(ParserA222, DriveStrengthHighz1Str0) {
  // ( highz1 , strength0 ): (highz1, weak0)
  auto r = Parse(
      "module m;\n"
      "  wire (highz1, weak0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 2u);  // weak0 = 2
  EXPECT_EQ(item->drive_strength1, 1u);  // highz1 = 1
}

// --- strength0 ---
// supply0 | strong0 | pull0 | weak0
TEST(ParserA222, Strength0AllKeywords) {
  // Verify all 4 strength0 keywords parse and map to correct values
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

// --- strength1 ---
// supply1 | strong1 | pull1 | weak1
TEST(ParserA222, Strength1AllKeywords) {
  // Verify all 4 strength1 keywords parse and map to correct values
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

// --- charge_strength ---
// ( small ) | ( medium ) | ( large )
TEST(ParserA222, ChargeStrengthSmall) {
  // trireg (small)
  auto r = Parse(
      "module m;\n"
      "  trireg (small) t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.charge_strength, 1u);
}

TEST(ParserA222, ChargeStrengthLarge) {
  // trireg (large)
  auto r = Parse(
      "module m;\n"
      "  trireg (large) t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.charge_strength, 4u);
}

// --- Strength value encoding verification ---
TEST(ParserA222, StrengthValueEncoding) {
  // Verify the full strength encoding: highz=1, weak=2, pull=3, strong=4,
  // supply=5 for both strength0 and strength1
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, pull1) w1;\n"
      "  wire (supply0, supply1) w2;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* w1 = r.cu->modules[0]->items[0];
  EXPECT_EQ(w1->drive_strength0, 2u);  // weak0
  EXPECT_EQ(w1->drive_strength1, 3u);  // pull1
  auto* w2 = r.cu->modules[0]->items[1];
  EXPECT_EQ(w2->drive_strength0, 5u);  // supply0
  EXPECT_EQ(w2->drive_strength1, 5u);  // supply1
}

// --- No drive strength (default) ---
TEST(ParserA222, NoDriveStrengthDefault) {
  // When no drive_strength specified, both should be 0 (none)
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

}  // namespace
