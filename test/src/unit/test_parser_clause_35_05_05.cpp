// §35.5.5: Function result

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA26, DpiImportFunctionVoid) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void c_print(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

// =============================================================================
// Annex H - DPI string return type
// =============================================================================
TEST_F(AnnexHParseTest, AnnexHDpiImportStringReturn) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function string get_version();\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "get_version");
  EXPECT_EQ(items[0]->return_type.kind, DataTypeKind::kString);
  EXPECT_TRUE(items[0]->dpi_is_pure);
}

}  // namespace
