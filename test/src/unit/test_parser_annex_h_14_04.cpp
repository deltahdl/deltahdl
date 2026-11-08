#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

class ExampleNineParsing : public ::testing::Test {
 protected:
  ParseResult r_ = Parse(
      "module m;\n"
      "  typedef struct {int x; int y;} pair;\n"
      "  import \"DPI\" function void f1(input int i1, pair i2,\n"
      "                                output logic [63:0] o3);\n"
      "  export \"DPI\" function exported_sv_func;\n"
      "  function void exported_sv_func(input int i, output int o [0:7]);\n"
      "    begin end\n"
      "  endfunction\n"
      "endmodule\n");
};

TEST_F(ExampleNineParsing, TheDeprecatedAnnotationWarnsAndParses) {
  ASSERT_NE(r_.cu, nullptr);
  EXPECT_FALSE(r_.has_errors);
  EXPECT_TRUE(ReportedWarning(
      r_.diags,
      "\"DPI\" is deprecated and should be replaced with \"DPI-C\"; use of the "
      "\"DPI-C\" string may require changes in the DPI application's C code",
      3, "35.5.4"));
  ASSERT_EQ(r_.cu->modules.size(), 1u);
}

TEST_F(ExampleNineParsing, TheImportAndExportCarryTheDpiSpecString) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f1 =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(f1, nullptr);
  EXPECT_EQ(f1->dpi_spec_string, "DPI");
  ASSERT_EQ(f1->func_args.size(), 3u);
  EXPECT_EQ(f1->func_args[1].data_type.type_name, "pair");
  EXPECT_EQ(f1->func_args[2].direction, Direction::kOutput);
  EXPECT_EQ(f1->func_args[2].data_type.kind, DataTypeKind::kLogic);
  const ModuleItem* exp =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiExport);
  ASSERT_NE(exp, nullptr);
  EXPECT_EQ(exp->dpi_spec_string, "DPI");
  EXPECT_EQ(exp->name, "exported_sv_func");
}

}  // namespace
