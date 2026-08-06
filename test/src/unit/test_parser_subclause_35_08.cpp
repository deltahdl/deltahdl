#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §35.8: an export declaration for a task names the SystemVerilog task being
// exported, so the parsed item carries that task_identifier as well as the
// task flag. The annex A.2.6 file carries the production-level case, which
// checks the task flag alone.
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

// §35.8: the optional c_identifier of an exported function (§35.7) applies to
// exported tasks as well, and defaults to the task's own name, so an explicit
// one is recorded beside the task_identifier rather than replacing it. The
// annex A.2.6 file carries the production-level case, which checks the task
// flag and the c_identifier alone.
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
