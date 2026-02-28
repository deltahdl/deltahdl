// §35.5.2: Pure functions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST_F(AnnexHParseTest, AnnexHDpiImportPure) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function real sin_approx(real x);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "sin_approx");
  EXPECT_TRUE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_task);
}

}  // namespace
