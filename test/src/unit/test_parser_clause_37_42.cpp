// §37.42: Task and function call

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST_F(AnnexHParseTest, AnnexKVpiSysGetValue) {
  auto* unit = Parse(
      "module m;\n"
      "  initial $display($time);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

}  // namespace
