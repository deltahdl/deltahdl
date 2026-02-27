// §35.7: Exported functions


#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"

#include "fixture_parser.h"

using namespace delta;

};

namespace {

// ---------------------------------------------------------------------------
// dpi_import_export: export variants
// ---------------------------------------------------------------------------
TEST(ParserA26, DpiExportFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(item->name, "sv_func");
  EXPECT_FALSE(item->dpi_is_task);
}

TEST(ParserA26, DpiExportWithCIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI-C\" c_name = function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(item->dpi_c_name, "c_name");
  EXPECT_EQ(item->name, "sv_func");
}

TEST(ParserA26, DpiExportDpiLegacy) {
  auto r = Parse(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI\" function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kDpiExport);
}

}  // namespace
