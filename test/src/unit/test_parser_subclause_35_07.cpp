#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "simulator/vpi.h"

using namespace delta;

namespace {

// §35.7: an export declaration names the SystemVerilog function being
// exported, so the parsed item carries that function_identifier and no task
// flag. The annex A.2.6 file carries the production-level case, which checks
// the task flag alone.
TEST(FunctionDeclParsing, DpiExportFunctionRecordsFunctionIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(item->name, "sv_func");
  EXPECT_FALSE(item->dpi_is_task);
}

// §35.7: the optional c_identifier supplies the name used from the foreign
// language and defaults to the function_identifier, so an explicit one is
// recorded beside the exported function's own name rather than replacing it.
// The annex A.2.6 file carries the production-level case, which checks the
// c_identifier alone.
TEST(FunctionDeclParsing, DpiExportCIdentifierBesideFunctionIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI-C\" c_name = function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(item->dpi_c_name, "c_name");
  EXPECT_EQ(item->name, "sv_func");
}

TEST(FunctionDeclParsing, DpiExportDpiLegacy) {
  auto r = Parse(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI\" function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kDpiExport);
}

// §35.7: class member functions cannot be exported. The parser rejects any
// attempt to place a DPI export declaration inside a class body because the
// only function it could designate from that scope is a class method.
TEST(DpiParsing, DpiExportInsideClassBodyIsError) {
  auto r = Parse(R"(
    class C;
      function void f(); endfunction
      export "DPI-C" function f;
    endclass
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "DPI export declaration is not allowed in class "
                            "scope; class member functions cannot be exported",
                            4, "35.7"));
}

// §35.7: Syntax 35-2 restricts dpi_spec_string to "DPI-C" or its deprecated
// "DPI" alias. An export declaration carrying any other string is rejected.
TEST(DpiParsing, DpiExportRejectsUnknownSpecString) {
  auto r = Parse(R"(
    module m;
      function void sv_func(); endfunction
      export "DPI-X" function sv_func;
    endmodule
  )");
  // §35.5.4 owns the dpi_spec_string report; the export path reuses it.
  EXPECT_TRUE(ReportedError(
      r.diags, "DPI specification string must be \"DPI-C\" or \"DPI\"", 4,
      "35.5.4"));
}

}  // namespace
