// §35.8: Exported tasks

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;
}
;

namespace {

TEST(ParserA26, DpiExportTask) {
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

}  // namespace
