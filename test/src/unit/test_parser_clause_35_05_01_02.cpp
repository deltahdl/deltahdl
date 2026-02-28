// §35.5.1.2: input, output, and inout arguments

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Annex H - DPI import with output/inout arguments
// =============================================================================
TEST_F(AnnexHParseTest, AnnexHDpiImportOutputArgs) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void get_data(\n"
      "    input int addr,\n"
      "    output int data,\n"
      "    inout int status\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "get_data");
  ASSERT_EQ(items[0]->func_args.size(), 3u);
  EXPECT_EQ(items[0]->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(items[0]->func_args[0].name, "addr");
  EXPECT_EQ(items[0]->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(items[0]->func_args[1].name, "data");
  EXPECT_EQ(items[0]->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(items[0]->func_args[2].name, "status");
}

}  // namespace
