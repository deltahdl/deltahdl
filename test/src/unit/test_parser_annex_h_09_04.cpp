#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(DpiContextExampleParsing, TheExamplesIntegerResultIsNotASmallValue) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context MyCFunc = function integer MapID(int "
      "portID);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(
      r.diags, "result type is not permitted for a DPI imported function", 2,
      "35.5.5"));
}

TEST(DpiContextExampleParsing, TheImportOfExampleOneIsAContextFunction) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context MyCFunc = function int MapID(int portID);\n"
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
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "portID");
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
}

}  // namespace
