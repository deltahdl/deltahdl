// §10.3.4: Continuous assignment strengths

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- Drive strength in continuous assign context ---
TEST(ParserA222, DriveStrengthContinuousAssign) {
  // drive_strength used with assign statement
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, pull1) w = 1'b1;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  EXPECT_EQ(item->drive_strength0, 4u);  // strong0 = 4
  EXPECT_EQ(item->drive_strength1, 3u);  // pull1 = 3
}

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

static std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

TEST(ParserA601, ContinuousAssign_DriveStrength) {
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

}  // namespace
