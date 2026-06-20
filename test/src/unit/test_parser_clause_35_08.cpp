#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(FunctionDeclParsing, DpiExportTask) {
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

// §35.8: the optional c_identifier of an exported function (§35.7) applies to
// exported tasks as well. A task export written with an explicit C linkage name
// parses to a DPI export carrying both the task flag and the recorded
// c_identifier, exactly as a function export would.
TEST(FunctionDeclParsing, DpiExportTaskWithCIdentifier) {
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
