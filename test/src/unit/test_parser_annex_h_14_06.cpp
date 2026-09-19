#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

// §H.14.6, the SystemVerilog side of Example 11: an export of myfunc
// annotated "DPI" and the function myfunc taking an output logic [31:0].
TEST(ExampleElevenParsing, TheExportAndItsFunctionParse) {
  auto r = Parse(
      "module m;\n"
      "  export \"DPI\" function myfunc;\n"
      "  function void myfunc(output logic [31:0] r);\n"
      "    begin end\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const ModuleItem* exp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiExport);
  ASSERT_NE(exp, nullptr);
  EXPECT_EQ(exp->name, "myfunc");
  EXPECT_EQ(exp->dpi_spec_string, "DPI");
  const ModuleItem* func =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(func, nullptr);
  EXPECT_EQ(func->name, "myfunc");
  ASSERT_EQ(func->func_args.size(), 1u);
  EXPECT_EQ(func->func_args[0].name, "r");
  EXPECT_EQ(func->func_args[0].direction, Direction::kOutput);
  EXPECT_EQ(func->func_args[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(func->func_args[0].data_type.packed_dim_left, nullptr);
}

}  // namespace
