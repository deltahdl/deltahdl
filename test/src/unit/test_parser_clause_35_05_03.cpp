// §35.5.3: Context tasks and functions

#include "fixture_config.h"
#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

namespace {

TEST(ParserSection38, DpiImportForVpiAccess) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context function void\n"
      "    set_value(input int handle, input int val);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* dpi = FindItemByKind(r, ModuleItemKind::kDpiImport);
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->name, "set_value");
  EXPECT_TRUE(dpi->dpi_is_context);
}

TEST(ParserSection38, DpiImportContextCallbackWithArgs) {
  // Context function with arguments typical for VPI callback registration
  auto r = Parse(R"(
    module m;
      import "DPI-C" context function int register_cb_wrapper(
        input int reason, input string user_data
      );
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_EQ(items[0]->name, "register_cb_wrapper");
}
TEST_F(DpiParseTest, ImportContextFunction) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" context function void set_val(input int v);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_EQ(items[0]->name, "set_val");
}

TEST(ParserSection13, DpiImportContextTask) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context task c_display(input int x);\n"
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
  EXPECT_TRUE(dpi->dpi_is_context);
  EXPECT_TRUE(dpi->dpi_is_task);
}

}  // namespace
