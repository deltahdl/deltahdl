#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast_module.h"
#include "parser/parser.h"

using namespace delta;

namespace {

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

TEST(DpiGlobalNameParsing, ImportGlobalNameStartingWithUnderscoreAccepted) {
  auto r = Parse(R"(
    module m;
      import "DPI-C" _legal_42 = function void sv_local();
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->dpi_c_name, "_legal_42");
}

TEST(DpiGlobalNameParsing, ImportGlobalNameWithDollarRejected) {
  auto r = Parse(R"(
    module m;
      import "DPI-C" foo$bar = function void sv_local();
    endmodule
  )");
  EXPECT_TRUE(ReportedError(
      r.diags, "DPI c_identifier must match [a-zA-Z_][a-zA-Z0-9_]*", 3,
      "35.5.4"));
}

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
  EXPECT_TRUE(ReportedError(
      diag.Diagnostics(), "DPI c_identifier must match [a-zA-Z_][a-zA-Z0-9_]*",
      2, "35.5.4"));
}

}  // namespace
