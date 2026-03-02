// Annex H.7.4: Basic types

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Annex H - DPI chandle return type
// =============================================================================
TEST_F(AnnexHParseTest, AnnexHDpiImportChandle) {
  // chandle is the opaque pointer type used for DPI handles.
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function chandle create_handle();\n"
      "  import \"DPI-C\" function void destroy_handle(chandle h);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "create_handle");
  EXPECT_EQ(items[0]->return_type.kind, DataTypeKind::kChandle);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[1]->name, "destroy_handle");
  ASSERT_EQ(items[1]->func_args.size(), 1u);
  EXPECT_EQ(items[1]->func_args[0].data_type.kind, DataTypeKind::kChandle);
}

}  // namespace
