#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

// §H.9.4, the SystemVerilog side of Example 1: an imported context-sensitive
// C function with the C name MyCFunc, called MapID in SystemVerilog, taking an
// int port identifier. The example writes its result as integer, which is
// not among the small values §35.5.5 (and §H.8.9) restricts an import's
// result to -- byte, shortint, int, longint, real, shortreal, chandle, string
// and scalar bit and logic -- so the declaration as written is reported
// against the normative clause, the annex's example being informative.
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

// With the result an int, the small value a port mapping fits, the example's
// declaration is accepted: a context import of C name MyCFunc named MapID in
// SystemVerilog, returning int and taking an int input portID. The context
// qualifier is what lets the C side retrieve its instance scope.
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
