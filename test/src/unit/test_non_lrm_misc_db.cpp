// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

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

// =============================================================================
// A.1.5 Configuration source text
// =============================================================================
// config_declaration: config name; design statement; endconfig
TEST(SourceText, ConfigDeclBasic) {
  auto r = Parse(
      "config cfg1;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* c = r.cu->configs[0];
  EXPECT_EQ(c->name, "cfg1");
  ASSERT_EQ(c->design_cells.size(), 1u);
  EXPECT_EQ(c->design_cells[0].first, "work");
  EXPECT_EQ(c->design_cells[0].second, "top");
  ASSERT_EQ(c->rules.size(), 1u);
  EXPECT_EQ(c->rules[0]->kind, ConfigRuleKind::kDefault);
}

// config_declaration with endconfig label
TEST(SourceText, ConfigDeclEndLabel) {
  auto r = Parse(
      "config cfg2;\n"
      "  design top;\n"
      "endconfig : cfg2\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg2");
}

// config_declaration with local_parameter_declaration
TEST(SourceText, ConfigDeclLocalParams) {
  auto r = Parse(
      "config cfg3;\n"
      "  localparam WIDTH = 8;\n"
      "  localparam DEPTH = 4;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->local_params.size(), 2u);
  EXPECT_EQ(c->local_params[0].first, "WIDTH");
  EXPECT_EQ(c->local_params[1].first, "DEPTH");
}

// design_statement: multiple cells, with and without library qualifier
TEST(SourceText, ConfigDesignMultipleCells) {
  auto r = Parse(
      "config cfg4;\n"
      "  design work.top lib2.sub cellonly;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->design_cells.size(), 3u);
  EXPECT_EQ(c->design_cells[0].first, "work");
  EXPECT_EQ(c->design_cells[0].second, "top");
  EXPECT_EQ(c->design_cells[1].first, "lib2");
  EXPECT_EQ(c->design_cells[1].second, "sub");
  // Unqualified cell: lib is empty
  EXPECT_EQ(c->design_cells[2].first, "");
  EXPECT_EQ(c->design_cells[2].second, "cellonly");
}

// config_rule_statement: default_clause liblist_clause
TEST(SourceText, ConfigRuleDefaultLiblist) {
  auto r = Parse(
      "config cfg5;\n"
      "  design top;\n"
      "  default liblist lib1 lib2 lib3;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(rule->liblist.size(), 3u);
  EXPECT_EQ(rule->liblist[0], "lib1");
  EXPECT_EQ(rule->liblist[1], "lib2");
  EXPECT_EQ(rule->liblist[2], "lib3");
}

// config_rule_statement: inst_clause liblist_clause with hierarchical inst_name
TEST(SourceText, ConfigRuleInstLiblist) {
  auto r = Parse(
      "config cfg6;\n"
      "  design top;\n"
      "  instance top.u1.u2 liblist mylib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1.u2");
  ASSERT_EQ(rule->liblist.size(), 1u);
  EXPECT_EQ(rule->liblist[0], "mylib");
}

// config_rule_statement: inst_clause use_clause
TEST(SourceText, ConfigRuleInstUse) {
  auto r = Parse(
      "config cfg7;\n"
      "  design top;\n"
      "  instance top.u1 use work.alt_cell;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1");
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "alt_cell");
}

// config_rule_statement: cell_clause liblist_clause
TEST(SourceText, ConfigRuleCellLiblist) {
  auto r = Parse(
      "config cfg8;\n"
      "  design top;\n"
      "  cell mylib.mycell liblist lib_a lib_b;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "mylib");
  EXPECT_EQ(rule->cell_name, "mycell");
  ASSERT_EQ(rule->liblist.size(), 2u);
  EXPECT_EQ(rule->liblist[0], "lib_a");
  EXPECT_EQ(rule->liblist[1], "lib_b");
}

// config_rule_statement: cell_clause use_clause with :config suffix
TEST(SourceText, ConfigRuleCellUseConfig) {
  auto r = Parse(
      "config cfg9;\n"
      "  design top;\n"
      "  cell flip_flop use work.ff_impl :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_name, "flip_flop");
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "ff_impl");
  EXPECT_TRUE(rule->use_config);
}

// use_clause: use with named_parameter_assignment
TEST(SourceText, ConfigUseNamedParams) {
  auto r = Parse(
      "config cfg10;\n"
      "  design top;\n"
      "  instance top.u1 use #(.WIDTH(16), .DEPTH(4));\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "WIDTH");
  EXPECT_EQ(rule->use_params[1].first, "DEPTH");
}

// use_clause: use [lib.] cell named_parameter_assignment (combined form)
TEST(SourceText, ConfigUseCellAndParams) {
  auto r = Parse(
      "config cfg11;\n"
      "  design top;\n"
      "  cell adder use work.fast_add #(.W(32)) :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "fast_add");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_TRUE(rule->use_config);
}

// Comprehensive: multiple rules of different kinds in one config
TEST(SourceText, ConfigMultipleRules) {
  auto r = Parse(
      "config cfg12;\n"
      "  design work.top;\n"
      "  default liblist work rtl;\n"
      "  instance top.dut use gate.dut_impl;\n"
      "  cell lib.ram liblist sram_lib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->rules.size(), 3u);
  EXPECT_EQ(c->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(c->rules[1]->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(c->rules[2]->kind, ConfigRuleKind::kCell);
}

// cell_clause: unqualified cell identifier (no library prefix)
TEST(SourceText, ConfigCellUnqualified) {
  auto r = Parse(
      "config cfg13;\n"
      "  design top;\n"
      "  cell mux4 use better_mux;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "");
  EXPECT_EQ(rule->cell_name, "mux4");
  EXPECT_EQ(rule->use_cell, "better_mux");
}

// description: config_declaration
TEST(SourceText, DescriptionConfig) {
  auto r = Parse(
      "config cfg;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

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

// =============================================================================
// §33.4.1.1 Design statement
// =============================================================================
TEST_F(ConfigTest, DesignStatementParsed) {
  auto* unit = Parse(R"(
    config cfg;
      design lib1.top;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  EXPECT_EQ(cfg->name, "cfg");
  ASSERT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_EQ(cfg->design_cells[0].first, "lib1");
  EXPECT_EQ(cfg->design_cells[0].second, "top");
}

TEST_F(ConfigTest, DesignStatementNoLib) {
  auto* unit = Parse(R"(
    config cfg;
      design top;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_TRUE(cfg->design_cells[0].first.empty());
  EXPECT_EQ(cfg->design_cells[0].second, "top");
}

TEST_F(ConfigTest, DesignStatementMultipleTopCells) {
  auto* unit = Parse(R"(
    config cfg;
      design lib1.top1 lib2.top2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->design_cells.size(), 2u);
  EXPECT_EQ(cfg->design_cells[0].first, "lib1");
  EXPECT_EQ(cfg->design_cells[0].second, "top1");
  EXPECT_EQ(cfg->design_cells[1].first, "lib2");
  EXPECT_EQ(cfg->design_cells[1].second, "top2");
}

// =============================================================================
// §33.4.1.2 Default clause (liblist)
// =============================================================================
TEST_F(ConfigTest, DefaultLiblist) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      default liblist lib1 lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->rules.size(), 1u);
  auto* rule = cfg->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(rule->liblist.size(), 2u);
  EXPECT_EQ(rule->liblist[0], "lib1");
  EXPECT_EQ(rule->liblist[1], "lib2");
}

TEST_F(ConfigTest, DefaultLiblistSingleLib) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      default liblist mylib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(rule->liblist.size(), 1u);
  EXPECT_EQ(rule->liblist[0], "mylib");
}

// =============================================================================
// §33.4.1.3 Instance clause with liblist
// =============================================================================
TEST_F(ConfigTest, InstanceLiblist) {
  auto* unit = Parse(R"(
    config cfg;
      design rtlLib.top;
      default liblist rtlLib;
      instance top.a2 liblist gateLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->rules.size(), 2u);

  auto* r0 = cfg->rules[0];
  EXPECT_EQ(r0->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(r0->liblist[0], "rtlLib");

  auto* r1 = cfg->rules[1];
  EXPECT_EQ(r1->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(r1->inst_path, "top.a2");
  ASSERT_EQ(r1->liblist.size(), 1u);
  EXPECT_EQ(r1->liblist[0], "gateLib");
}

// =============================================================================
// §33.4.1.3/6 Instance clause with use binding
// =============================================================================
TEST_F(ConfigTest, InstanceUseClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib1.top;
      instance top.u1 use lib2.adder;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1");
  EXPECT_EQ(rule->use_lib, "lib2");
  EXPECT_EQ(rule->use_cell, "adder");
  EXPECT_FALSE(rule->use_config);
}

// =============================================================================
// §33.4.1.4/5 Cell clause for library binding
// =============================================================================
TEST_F(ConfigTest, CellClauseLiblist) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      cell adder liblist lib2 lib3;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_TRUE(rule->cell_lib.empty());
  EXPECT_EQ(rule->cell_name, "adder");
  ASSERT_EQ(rule->liblist.size(), 2u);
  EXPECT_EQ(rule->liblist[0], "lib2");
  EXPECT_EQ(rule->liblist[1], "lib3");
}

TEST_F(ConfigTest, CellClauseWithLibUse) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      cell mylib.adder use otherlib.fast_adder;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "mylib");
  EXPECT_EQ(rule->cell_name, "adder");
  EXPECT_EQ(rule->use_lib, "otherlib");
  EXPECT_EQ(rule->use_cell, "fast_adder");
}

// =============================================================================
// §33.4.2 Config with nested config references
// =============================================================================
TEST_F(ConfigTest, NestedConfigReference) {
  auto* unit = Parse(R"(
    config bot;
      design lib1.bot;
      default liblist lib1 lib2;
    endconfig
    config top;
      design lib1.top;
      instance top.bot use lib1.bot :config;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 2u);
  EXPECT_EQ(unit->configs[0]->name, "bot");
  EXPECT_EQ(unit->configs[1]->name, "top");

  ASSERT_EQ(unit->configs[1]->rules.size(), 1u);
  auto* rule = unit->configs[1]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->use_lib, "lib1");
  EXPECT_EQ(rule->use_cell, "bot");
  EXPECT_TRUE(rule->use_config);
}

// =============================================================================
// §33.3 Library mapping (parsing only)
// =============================================================================
TEST_F(ConfigTest, LibraryMappingConfig) {
  // Config with library-qualified design cells
  auto* unit = Parse(R"(
    config cfg;
      design rtlLib.top;
      default liblist rtlLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_EQ(cfg->design_cells[0].first, "rtlLib");
  EXPECT_EQ(cfg->design_cells[0].second, "top");
  ASSERT_EQ(cfg->rules.size(), 1u);
  EXPECT_EQ(cfg->rules[0]->liblist[0], "rtlLib");
}

// =============================================================================
// §33.4.3 Config with parameter override
// =============================================================================
TEST_F(ConfigTest, UseClauseWithParams) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      instance top.u1 use lib.adder #(.WIDTH(16), .DEPTH(4));
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_EQ(unit->configs[0]->rules.size(), 1u);
  auto* rule = unit->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->use_lib, "lib");
  EXPECT_EQ(rule->use_cell, "adder");
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "WIDTH");
  EXPECT_EQ(rule->use_params[1].first, "DEPTH");
}

TEST_F(ConfigTest, LocalparamInConfig) {
  auto* unit = Parse(R"(
    config cfg;
      localparam W = 32;
      design lib.top;
      default liblist lib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->local_params.size(), 1u);
  EXPECT_EQ(cfg->local_params[0].first, "W");
  EXPECT_NE(cfg->local_params[0].second, nullptr);
}

// =============================================================================
// Multiple rules in single config
// =============================================================================
TEST_F(ConfigTest, MultipleRulesInConfig) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      default liblist rtlLib;
      instance top.a1 use lib.fast_adder;
      cell mux use lib.fast_mux;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  auto* cfg = unit->configs[0];
  ASSERT_EQ(cfg->rules.size(), 3u);
  EXPECT_EQ(cfg->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(cfg->rules[1]->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(cfg->rules[2]->kind, ConfigRuleKind::kCell);
}

// =============================================================================
// Endconfig with label
// =============================================================================
TEST_F(ConfigTest, EndconfigWithLabel) {
  auto* unit = Parse(R"(
    config my_config;
      design lib.top;
    endconfig : my_config
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "my_config");
  EXPECT_FALSE(HasErrors());
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

// =============================================================================
// LRM section 34.5.6 -- author_info pragma: config declarations with libraries
// These tests verify that configuration declarations (which reference library
// mappings) parse correctly alongside other design units.
// =============================================================================
TEST(ParserSection34, ConfigWithDefaultLiblist) {
  // Config with default clause specifying a library list
  auto r = Parse(R"(
    config cfg1;
      design mylib.top;
      default liblist mylib rtllib;
    endconfig
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg1");
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

using DpiParseTest = ProgramTestParse;

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
