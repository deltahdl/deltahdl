#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(FunctionDeclParsing, DpiExportTaskRecordsTaskIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  task sv_task(); endtask\n"
      "  export \"DPI-C\" task sv_task;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_TRUE(item->dpi_is_task);
  EXPECT_EQ(item->name, "sv_task");
}

TEST(FunctionDeclParsing, DpiExportCIdentifierBesideTaskIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  task sv_task(); endtask\n"
      "  export \"DPI-C\" c_task = task sv_task;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_TRUE(item->dpi_is_task);
  EXPECT_EQ(item->name, "sv_task");
  EXPECT_EQ(item->dpi_c_name, "c_task");
}

}  // namespace
