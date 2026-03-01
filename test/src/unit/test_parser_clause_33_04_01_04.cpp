// §33.4.1.4: The cell clause

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// =============================================================================
// §36.9.1 Config library (cell clause)
// =============================================================================
TEST_F(ApiParseTest, ConfigCellClauseLiblist) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      cell adder liblist lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* cell_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(cell_rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cell_rule->cell_name, "adder");
  ASSERT_EQ(cell_rule->liblist.size(), 1u);
  EXPECT_EQ(cell_rule->liblist[0], "lib2");
}

TEST_F(ApiParseTest, ConfigCellClauseWithLib) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      cell gateLib.adder use rtlLib.adder;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* cell_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(cell_rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cell_rule->cell_lib, "gateLib");
  EXPECT_EQ(cell_rule->cell_name, "adder");
  EXPECT_EQ(cell_rule->use_lib, "rtlLib");
  EXPECT_EQ(cell_rule->use_cell, "adder");
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

struct ParseResult31 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31 Parse(const std::string& src) {
  ParseResult31 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using ConfigParseTest = ProgramTestParse;

TEST_F(ConfigParseTest, ConfigWithCellClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      cell top use lib.other;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

}  // namespace
