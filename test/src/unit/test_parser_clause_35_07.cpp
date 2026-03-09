#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "simulator/vpi.h"

using namespace delta;

namespace {

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

TEST_F(AnnexHParseTest, AnnexHDpiExportFunction) {
  auto* unit = Parse(
      "module m;\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "sv_func");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST_F(DpiParseTest, ExportWithCName) {
  auto* unit = Parse(R"(
    module m;
      export "DPI-C" c_func = function sv_func;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_func");
  EXPECT_EQ(items[0]->name, "sv_func");
}

TEST_F(AnnexHParseTest, AnnexHDpiExportWithCName) {
  auto* unit = Parse(
      "module m;\n"
      "  export \"DPI-C\" my_c_func = function sv_compute;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->dpi_c_name, "my_c_func");
  EXPECT_EQ(items[0]->name, "sv_compute");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST(ParserSection38, DpiExportFunctionForCalltf) {
  auto r = Parse(R"(
    module m;
      export "DPI-C" function calltf_routine;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "calltf_routine");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST(ParserSection38, DpiExportWithCNameForSystf) {
  auto r = Parse(R"(
    module m;
      export "DPI-C" my_c_calltf = function sv_calltf;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->dpi_c_name, "my_c_calltf");
  EXPECT_EQ(items[0]->name, "sv_calltf");
}

TEST_F(DpiParseTest, ExportFunction) {
  auto* unit = Parse(R"(
    module m;
      export "DPI-C" function my_func;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "my_func");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

}  // namespace
