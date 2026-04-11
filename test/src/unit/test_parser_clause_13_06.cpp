#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ImportExportParsing, ImportFunctionDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->name, "c_add");
  EXPECT_FALSE(item->dpi_is_task);
}

TEST(ImportExportParsing, ImportTaskDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" task c_print(int val);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->name, "c_print");
  EXPECT_TRUE(item->dpi_is_task);
}

TEST(ImportExportParsing, ExportFunctionDeclaration) {
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

TEST(ImportExportParsing, ExportTaskDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  task sv_task(); endtask\n"
      "  export \"DPI-C\" task sv_task;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(item->name, "sv_task");
  EXPECT_TRUE(item->dpi_is_task);
}

TEST(ImportExportParsing, ImportedFunctionCalledWithNormalSyntax) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "  int x;\n"
      "  initial x = c_add(1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ImportExportParsing, ImportAndExportCoexist) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_func(int x);\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(r.cu->modules[0]->items[2]->kind, ModuleItemKind::kDpiExport);
}

TEST(ImportExportParsing, ImportedFunctionUsedInExpression) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_mul(int a, int b);\n"
      "  int y;\n"
      "  initial y = c_mul(3, 4) + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
