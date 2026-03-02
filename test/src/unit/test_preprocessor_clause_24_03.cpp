// §24.3: The program construct

#include "fixture_parser.h"

using namespace delta;

static bool HasItemOfKind(const std::vector<ModuleItem*>& items,
                          ModuleItemKind kind) {
  for (const auto* item : items)
    if (item->kind == kind) return true;
  return false;
}

namespace {

// =============================================================================
// LRM §3.4 — Programs
// =============================================================================
// §3.4 LRM example (verbatim) with end label:
//   program test (input clk, input [16:1] addr, inout [7:0] data);
//   initial begin ... end
//   endprogram : test
TEST(ParserClause03, Cl3_4_LrmExample) {
  auto r = ParseWithPreprocessor(
      "program test (input clk, input [16:1] addr, inout [7:0] data);\n"
      "  initial begin\n"
      "  end\n"
      "endprogram : test\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test");
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->programs[0]->ports[1].name, "addr");
  EXPECT_EQ(r.cu->programs[0]->ports[2].name, "data");
  EXPECT_EQ(r.cu->programs[0]->ports[2].direction, Direction::kInout);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

}  // namespace
