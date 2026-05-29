#include "fixture_parser.h"

using namespace delta;

namespace {

// §35.4: an explicit global name "in addition to its declared name" is given
// before the '=' in an import or export declaration. The parser records the
// global name on dpi_c_name and the local SystemVerilog name on name, which
// keeps the two name spaces distinct as the clause requires.

TEST(DpiGlobalNameParsing, ImportExplicitGlobalNameDistinctFromSvName) {
  auto r = Parse(R"(
    module m;
      import "DPI-C" gname = function void sv_local();
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->dpi_c_name, "gname");
  EXPECT_EQ(item->name, "sv_local");
}

TEST(DpiGlobalNameParsing, ExportExplicitGlobalNameDistinctFromSvName) {
  auto r = Parse(R"(
    module m;
      export "DPI-C" gname = function sv_local;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(item->dpi_c_name, "gname");
  EXPECT_EQ(item->name, "sv_local");
}

// §35.4: when no global name is given, the linkage identifier defaults to the
// SystemVerilog subroutine name. The parser models this by leaving dpi_c_name
// empty; the downstream consumer treats an empty dpi_c_name as the request to
// fall back on item->name.
TEST(DpiGlobalNameParsing, ImportWithoutGlobalNameLeavesDpiCNameEmpty) {
  auto r = Parse(R"(
    module m;
      import "DPI-C" function void plain();
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_c_name.empty());
  EXPECT_EQ(item->name, "plain");
}

TEST(DpiGlobalNameParsing, ExportWithoutGlobalNameLeavesDpiCNameEmpty) {
  auto r = Parse(R"(
    module m;
      export "DPI-C" function plain;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_c_name.empty());
  EXPECT_EQ(item->name, "plain");
}

// §35.4: "Should a global name clash with a SystemVerilog keyword or a
// reserved name, it shall take the form of an escaped identifier." The lexer
// strips the leading '\' and the trailing whitespace; the linkage identifier
// the parser records is the bare keyword text.
TEST(DpiGlobalNameParsing, ImportEscapedGlobalNameOfKeywordIsRecorded) {
  auto r = Parse(R"(
    module m;
      import "DPI-C" \if = function void sv_local();
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->dpi_c_name, "if");
  EXPECT_EQ(item->name, "sv_local");
}

TEST(DpiGlobalNameParsing, ExportEscapedGlobalNameOfKeywordIsRecorded) {
  auto r = Parse(R"(
    module m;
      export "DPI-C" \class = function sv_local;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->dpi_c_name, "class");
  EXPECT_EQ(item->name, "sv_local");
}

// §35.4: "After this stripping, the linkage identifier so formed shall comply
// with the normal rules for C identifier construction." A name whose first
// character is a digit fails the C rule even though escaping made it lexable
// as a SystemVerilog identifier.
TEST(DpiGlobalNameParsing, EscapedNameStartingWithDigitIsRejected) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>",
                         "module m;\n"
                         "  import \"DPI-C\" \\1bad = function void f();\n"
                         "endmodule\n");
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  EXPECT_TRUE(diag.HasErrors());
}

}  // namespace
