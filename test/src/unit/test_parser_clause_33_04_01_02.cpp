// §33.4.1.2: The default clause

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

}  // namespace
