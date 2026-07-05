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

TEST(StrengthParsing, SameDirectionStrength0PairRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire (weak0, strong0) w;\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(StrengthParsing, SameDirectionStrength1PairRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire (pull1, supply1) w;\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(StrengthParsing, Highz0WithStrength0Rejected) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz0, weak0) w;\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(StrengthParsing, Highz1WithStrength1Rejected) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz1, weak1) w;\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(StrengthParsing, Highz0Highz1ParsesAtParserStage) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz0, highz1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1u);
  EXPECT_EQ(item->drive_strength1, 1u);
}

TEST(StrengthParsing, Highz1Highz0ParsesAtParserStage) {
  auto r = Parse(
      "module m;\n"
      "  wire (highz1, highz0) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1u);
  EXPECT_EQ(item->drive_strength1, 1u);
}

TEST(StrengthParsing, ContAssignSameDirectionPairRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak0) w = 1'b0;\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(StrengthParsing, UdpInstSingleStrengthRejected) {
  auto r = Parse(
      "primitive my_udp(output y, input a);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  my_udp (weak0) u1(y, a);\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

TEST(StrengthParsing, UdpInstSameDirectionPairRejected) {
  auto r = Parse(
      "primitive my_udp(output y, input a);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  my_udp (weak0, weak0) u1(y, a);\n"
      "endmodule");
  EXPECT_TRUE(r.has_errors);
}

// Positive input form for drive_strength in UDP-instantiation position: a
// valid strength0/strength1 pair is accepted and stored on the instance. The
// existing UDP tests only exercise the reject paths, so this covers the accept
// side of the same syntactic position.
TEST(StrengthParsing, UdpInstDriveStrengthAccepted) {
  auto r = Parse(
      "primitive my_udp(output y, input a);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire y, a;\n"
      "  my_udp (strong0, weak1) u1(y, a);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleItem* inst = nullptr;
  for (auto* it : r.cu->modules[0]->items) {
    if (it->kind == ModuleItemKind::kUdpInst) inst = it;
  }
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->drive_strength0, 4u);  // strong0
  EXPECT_EQ(inst->drive_strength1, 2u);  // weak1
}

TEST(ChargeStrengthParsing, Small) {
  auto r = Parse(
      "module m;\n"
      "  trireg (small) cap;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.charge_strength, 1u);
}

TEST(ChargeStrengthParsing, Medium) {
  auto r = Parse(
      "module m;\n"
      "  trireg (medium) cap;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.charge_strength, 2u);
}

TEST(ChargeStrengthParsing, Large) {
  auto r = Parse(
      "module m;\n"
      "  trireg (large) cap;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.charge_strength, 4u);
}

}  // namespace
