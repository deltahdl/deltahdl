// §33.4.1.1: Design statement

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

}  // namespace
