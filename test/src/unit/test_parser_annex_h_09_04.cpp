#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §H.9.4, the SystemVerilog side of Example 1: an imported context-sensitive
// C function with the C name MyCFunc, called MapID in SystemVerilog, taking an
// int port identifier and returning an integer. The declaration carries the
// context qualifier that lets the C side retrieve its instance scope.
TEST(DpiContextExampleParsing, TheImportOfExampleOneIsAContextFunction) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context MyCFunc = function integer MapID(int "
      "portID);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const ModuleItem* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "MapID");
  EXPECT_EQ(item->dpi_c_name, "MyCFunc");
  EXPECT_TRUE(item->dpi_is_context);
  EXPECT_FALSE(item->dpi_is_pure);
  EXPECT_FALSE(item->dpi_is_task);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInteger);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "portID");
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
}

}  // namespace
