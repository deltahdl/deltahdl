// §30.4.4.4: The ifnone condition

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ifnone simple_path_declaration
TEST(ParserA702, StateDependentIfnoneSimple) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    ifnone (a => b) = 15;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
}
using ConfigParseTest = ProgramTestParse;

TEST_F(SpecifyTest, IfnoneConditionalPath) {
  auto *cu = Parse("module m;\n"
                   "specify\n"
                   "  ifnone (a => b) = 7;\n"
                   "endspecify\n"
                   "endmodule\n");
  auto *spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_TRUE(spec->specify_items[0]->path.is_ifnone);
  EXPECT_EQ(spec->specify_items[0]->path.condition, nullptr);
}
SpecifyItem *GetSolePathItem(ParseResult &r) {
  if (!r.cu || r.cu->modules.empty())
    return nullptr;
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty())
    return nullptr;
  return spec->specify_items[0];
}

// path_declaration ::= state_dependent_path_declaration ; (ifnone)
TEST(ParserA702, PathDeclStateDependentIfnone) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    ifnone (a => b) = 15;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
}

// § module_path_conditional_expression used in specify ifnone
TEST(ParserA83, ModulePathConditionalInSpecify) {
  auto r = Parse("module m(input a, input en, output y);\n"
                 "  specify\n"
                 "    if (en) (a => y) = 2;\n"
                 "    ifnone (a => y) = 3;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

using SpecifyParseTest = ProgramTestParse;

// =============================================================================
// Parser test fixture
// =============================================================================
struct SpecifyTest : ::testing::Test {
protected:
  CompilationUnit *Parse(const std::string &src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  // Helper: get first specify block from first module.
  ModuleItem *FirstSpecifyBlock(CompilationUnit *cu) {
    for (auto *item : cu->modules[0]->items) {
      if (item->kind == ModuleItemKind::kSpecifyBlock)
        return item;
    }
    return nullptr;
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};
TEST(ParserSection28, Sec28_12_IfnonePath) {
  auto sp = ParseSpecifySingle("module m(input a, output b);\n"
                               "  specify\n"
                               "    ifnone (a => b) = 15;\n"
                               "  endspecify\n"
                               "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto *si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

} // namespace
