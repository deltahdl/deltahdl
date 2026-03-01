// §33.4.1.3: The instance clause

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

// =============================================================================
// §36.9.2 Config instance clause
// =============================================================================
TEST_F(ApiParseTest, ConfigInstanceClauseLiblist) {
  auto* unit = Parse(R"(
    config cfg1;
      design rtlLib.top;
      default liblist rtlLib;
      instance top.a2 liblist gateLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->inst_path, "top.a2");
  ASSERT_EQ(inst_rule->liblist.size(), 1u);
  EXPECT_EQ(inst_rule->liblist[0], "gateLib");
}

}  // namespace
