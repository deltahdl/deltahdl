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
