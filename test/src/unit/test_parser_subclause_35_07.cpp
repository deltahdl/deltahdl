#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

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

TEST(DpiParsing, DpiExportRejectsUnknownSpecString) {
  auto r = Parse(R"(
    module m;
      function void sv_func(); endfunction
      export "DPI-X" function sv_func;
    endmodule
  )");
  EXPECT_TRUE(ReportedError(
      r.diags, "DPI specification string must be \"DPI-C\" or \"DPI\"", 4,
      "35.5.4"));
}

}  // namespace
