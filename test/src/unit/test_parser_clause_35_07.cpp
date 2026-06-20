#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "simulator/vpi.h"

using namespace delta;

namespace {

TEST(FunctionDeclParsing, DpiExportFunction) {
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

TEST(FunctionDeclParsing, DpiExportWithCIdentifier) {
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
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
