// §35.7: Exported functions

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;

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

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
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

// =============================================================================
// Annex H - DPI export with C name alias
// =============================================================================
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

// =============================================================================
// LRM section 38.37 -- vpi_register_systf: DPI-C exports for system tasks
// These tests verify DPI-C export declarations modeling the callback
// registration pattern used by vpi_register_systf().
// =============================================================================
TEST(ParserSection38, DpiExportFunctionForCalltf) {
  // Export an SV function for C-side systf registration
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
  // Export with explicit C-side name for systf registration
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

}  // namespace
