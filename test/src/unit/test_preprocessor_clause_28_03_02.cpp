#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(GateLevelModelingParsing, StrengthWithDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and (strong0, strong1) #5 g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 4);
  EXPECT_EQ(item->drive_strength1, 4);
  EXPECT_NE(item->gate_delay, nullptr);
  ASSERT_EQ(item->gate_terminals.size(), 3);
}

TEST(GateLevelModelingParsing, StrengthSpec) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and (strong0, weak1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->drive_strength0, 4);
  EXPECT_EQ(item->drive_strength1, 2);
  EXPECT_EQ(item->gate_inst_name, "g1");
}

TEST(GateLevelModelingParsing, StrengthSpecSupply) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nand (supply0, supply1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 5);
  EXPECT_EQ(item->drive_strength1, 5);
}

TEST(GateLevelModelingParsing, StrengthSpecHighz) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  or (highz0, pull1) g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 1);
  EXPECT_EQ(item->drive_strength1, 3);
}

TEST(GateDriveStrength, StrengthAndDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, strong1) #10 g1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);
  EXPECT_EQ(g->drive_strength1, 4u);
  EXPECT_NE(g->gate_delay, nullptr);
}

}  // namespace
