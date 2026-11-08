#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

class ExampleTenParsing : public ::testing::Test {
 protected:
  ParseResult r_ = Parse(
      "module m;\n"
      "  typedef struct {int a; bit [6:1][1:8] b [65:2]; int c;} triple;\n"
      "  import \"DPI\" function void f1(input triple t);\n"
      "  export \"DPI\" function exported_sv_func;\n"
      "  function void exported_sv_func(input int i, output logic [63:0] o);\n"
      "    begin end\n"
      "  endfunction\n"
      "endmodule\n");
};

TEST_F(ExampleTenParsing, TheDeprecatedAnnotationWarnsAndParses) {
  ASSERT_NE(r_.cu, nullptr);
  EXPECT_FALSE(r_.has_errors);
  EXPECT_TRUE(ReportedWarning(
      r_.diags,
      "\"DPI\" is deprecated and should be replaced with \"DPI-C\"; use of the "
      "\"DPI-C\" string may require changes in the DPI application's C code",
      3, "35.5.4"));
}

TEST_F(ExampleTenParsing, TheImportTakesTheTripleAndTheExportIsNamed) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f1 =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(f1, nullptr);
  EXPECT_EQ(f1->dpi_spec_string, "DPI");
  ASSERT_EQ(f1->func_args.size(), 1u);
  EXPECT_EQ(f1->func_args[0].data_type.type_name, "triple");
  const ModuleItem* exp =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiExport);
  ASSERT_NE(exp, nullptr);
  EXPECT_EQ(exp->dpi_spec_string, "DPI");
  EXPECT_EQ(exp->name, "exported_sv_func");
}

}  // namespace
