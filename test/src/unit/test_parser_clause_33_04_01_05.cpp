// §33.4.1.5: The liblist clause

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

}  // namespace
