// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

struct ConfigTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  bool HasErrors() const { return diag_.HasErrors(); }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

struct ParseResult34 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult34 Parse(const std::string& src) {
  ParseResult34 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

using DpiParseTest = ProgramTestParse;

namespace {

// =============================================================================
// A.1.1 include_statement ::= include file_path_spec ;
// =============================================================================
// Basic include statement.
TEST(LibraryText, IncludeStatement) {
  auto r = ParseLibrary("include /proj/other.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_EQ(r.cu->lib_includes[0]->file_path, "/proj/other.map");
}

// Include statement with relative path.
TEST(LibraryText, IncludeStatementRelative) {
  auto r = ParseLibrary("include ./sub/lib.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_EQ(r.cu->lib_includes[0]->file_path, "./sub/lib.map");
}

// =============================================================================
// A.1.1 library_description ::=
//   library_declaration | include_statement | config_declaration | ;
// =============================================================================
// Multiple library descriptions mixed together.
TEST(LibraryText, MixedDescriptions) {
  auto r = ParseLibrary(
      "library lib1 /a/*.v;\n"
      ";\n"
      "include /proj/other.map;\n"
      "library lib2 /b/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->name, "lib1");
  EXPECT_EQ(r.cu->libraries[1]->name, "lib2");
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
}

// =============================================================================
// Comments in library source text.
// =============================================================================
// Line comments.
TEST(LibraryText, LineComments) {
  auto r = ParseLibrary(
      "// This is a library map file\n"
      "library lib1 /proj/*.v; // RTL files\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
}

// Block comments.
TEST(LibraryText, BlockComments) {
  auto r = ParseLibrary(
      "/* Multi-line\n"
      "   comment */\n"
      "library lib1 /proj/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
}

// =============================================================================
// AST structural verification — ensures AST nodes capture all data.
// =============================================================================
// Verify LibraryDecl stores source range.
TEST(LibraryText, LibraryDeclHasSourceRange) {
  auto r = ParseLibrary("library mylib /proj/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_NE(r.cu->libraries[0]->range.start.line, 0u);
}

// Verify IncludeStmt stores source location.
TEST(LibraryText, IncludeStmtHasSourceLoc) {
  auto r = ParseLibrary("include /proj/lib.map;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  EXPECT_NE(r.cu->lib_includes[0]->loc.line, 0u);
}

// =============================================================================
// Multiple library declarations.
// =============================================================================
// Multiple libraries, each mapping different file patterns.
TEST(LibraryText, MultipleLibraries) {
  auto r = ParseLibrary(
      "library rtlLib *.v;\n"
      "library gateLib ./*.vg;\n"
      "library tbLib ../tb/*.sv;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 3u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  EXPECT_EQ(r.cu->libraries[1]->name, "gateLib");
  EXPECT_EQ(r.cu->libraries[2]->name, "tbLib");
}

// =============================================================================
// Error handling.
// =============================================================================
// Missing semicolon after library declaration.
TEST(LibraryText, ErrorMissingSemicolon) {
  auto r = ParseLibrary("library lib /proj/*.v\n");
  EXPECT_TRUE(r.has_errors);
}

// Missing file path spec.
TEST(LibraryText, ErrorMissingFilePath) {
  auto r = ParseLibrary("library lib;\n");
  // Should produce an error: file_path_spec is required.
  EXPECT_TRUE(r.has_errors);
}

// Missing library identifier.
TEST(LibraryText, ErrorMissingLibraryName) {
  auto r = ParseLibrary("library;\n");
  EXPECT_TRUE(r.has_errors);
}

// Include without file path.
TEST(LibraryText, ErrorIncludeNoPath) {
  auto r = ParseLibrary("include;\n");
  EXPECT_TRUE(r.has_errors);
}

// =============================================================================
// LRM §33 examples — library map file from the specification.
// =============================================================================
// LRM example: library rtlLib *.v;
TEST(LibraryText, LrmExampleSimple) {
  auto r = ParseLibrary("library rtlLib *.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "*.v");
}

// LRM example: library gateLib ./*.vg;
TEST(LibraryText, LrmExampleDotSlash) {
  auto r = ParseLibrary("library gateLib ./*.vg;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "gateLib");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./*.vg");
}

// LRM comprehensive example with all features.
TEST(LibraryText, LrmComprehensiveExample) {
  auto r = ParseLibrary(
      "// Library map file\n"
      "library rtlLib /proj/rtl/*.v, /proj/common/*.v\n"
      "  -incdir /proj/inc, /proj/common/inc;\n"
      "library gateLib /proj/gates/*.vg;\n"
      "include /proj/sub_libs.map;\n"
      "config top_cfg;\n"
      "  design rtlLib.top;\n"
      "  default liblist rtlLib gateLib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 2u);
  ASSERT_EQ(r.cu->lib_includes.size(), 1u);
  ASSERT_EQ(r.cu->configs.size(), 1u);
}

// =============================================================================
// Lexer: file_path_spec token recognition.
// =============================================================================
// Verify the lexer correctly reads file path specs with special chars.
TEST(LibraryText, LexerFilePathSpecAbsolute) {
  auto r = ParseLibrary("library lib /proj/rtl/top.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/top.v");
}

// File path spec with parent directory (..).
TEST(LibraryText, LexerFilePathSpecParentDir) {
  auto r = ParseLibrary("library lib ../rtl/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "../rtl/*.v");
}

// Config declaration within library text.
TEST(LibraryText, ConfigInLibraryText) {
  auto r = ParseLibrary(
      "library lib1 /a/*.v;\n"
      "config cfg;\n"
      "  design lib1.top;\n"
      "  default liblist lib1;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(ParserSection34, ConfigWithMultipleLibraries) {
  // Config referencing multiple libraries in liblist
  auto r = Parse(R"(
    config design_cfg;
      design lib1.chip_top;
      default liblist lib1 lib2 lib3;
      instance chip_top.cpu liblist lib2;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* cfg = r.cu->configs[0];
  EXPECT_EQ(cfg->name, "design_cfg");
  // Should have design cells
  ASSERT_GE(cfg->design_cells.size(), 1u);
}

TEST(ParserSection34, ConfigWithUseClause) {
  // Config with use clause to specify library cell binding
  auto r = Parse(R"(
    config map_cfg;
      design work.top;
      cell ram_cell use gatelib.ram_gate;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "map_cfg");
  ASSERT_GE(r.cu->configs[0]->rules.size(), 1u);
}

TEST(ParserSection34, ConfigWithInstanceAndLiblist) {
  // Config with instance clause pointing to a specific library
  auto r = Parse(R"(
    config inst_cfg;
      design work.top;
      instance top.u1 liblist gatelib;
      instance top.u2 liblist rtllib;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* cfg = r.cu->configs[0];
  ASSERT_GE(cfg->rules.size(), 2u);
}

TEST(ParserSection34, ConfigCoexistsWithModuleAndProtected) {
  // Ensure config declarations coexist with modules
  // (In a full flow, protected modules are stripped by preprocessor;
  //  at parser level, we verify both units parse alongside each other.)
  auto r = Parse(R"(
    module protected_ip;
      logic [7:0] data;
    endmodule

    config ip_cfg;
      design work.protected_ip;
      default liblist work;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "protected_ip");
  EXPECT_EQ(r.cu->configs[0]->name, "ip_cfg");
}

// =============================================================================
// §35.3 DPI-C import declarations
// =============================================================================
TEST_F(DpiParseTest, ImportFunction) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" function int add(input int a, input int b);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "add");
  EXPECT_FALSE(items[0]->dpi_is_task);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
}

TEST_F(DpiParseTest, ImportTask) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" task do_something();
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "do_something");
  EXPECT_TRUE(items[0]->dpi_is_task);
}

TEST_F(DpiParseTest, ImportWithCName) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" c_add = function int add(input int a, input int b);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_add");
  EXPECT_EQ(items[0]->name, "add");
}

TEST_F(DpiParseTest, ImportPureFunction) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" pure function int get_val();
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
  EXPECT_EQ(items[0]->name, "get_val");
}

TEST_F(DpiParseTest, ImportContextFunction) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" context function void set_val(input int v);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_EQ(items[0]->name, "set_val");
}

// =============================================================================
// §35.3 DPI-C export declarations
// =============================================================================
TEST_F(DpiParseTest, ExportFunction) {
  auto* unit = Parse(R"(
    module m;
      export "DPI-C" function my_func;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "my_func");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

}  // namespace
