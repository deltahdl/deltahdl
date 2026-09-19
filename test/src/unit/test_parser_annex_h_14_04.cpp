#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

// §H.14.4, the SystemVerilog side of Example 9: the declarations of
// §H.10.2's Example 2 annotated "DPI" rather than "DPI-C" -- a typedef
// struct pair, an import f1 taking an int, a pair and an output logic
// [63:0], an export of exported_sv_func and that function taking an int and
// an output unpacked array of eight ints -- selecting the deprecated SV3.1a
// argument passing semantics per §H.14.1.
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

// §H.14.4 with §35.5.4: the "DPI" annotation is deprecated and draws the
// warning that says so, and the module parses under it.
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

// The import and the export carry the "DPI" spec string the semantics are
// selected from, and f1's formals are the example's three.
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
