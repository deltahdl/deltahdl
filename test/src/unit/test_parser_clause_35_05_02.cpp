#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

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

TEST_F(DpiParseTest, ImportPureFunction) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" pure function int get_val();
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
  EXPECT_EQ(items[0]->name, "get_val");
}

TEST(ParserSection13, DpiImportPureFunction) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function int c_mul(int a, int b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->dpi_is_pure);
  EXPECT_FALSE(dpi->dpi_is_context);
}

}
