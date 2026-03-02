// §30.4.4.4: The ifnone condition

#include "fixture_parser.h"

using namespace delta;

namespace {

// ifnone simple_path_declaration
TEST(ParserA702, StateDependentIfnoneSimple) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
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

TEST_F(SpecifyTest, IfnoneConditionalPath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  ifnone (a => b) = 7;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_TRUE(spec->specify_items[0]->path.is_ifnone);
  EXPECT_EQ(spec->specify_items[0]->path.condition, nullptr);
}

ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

SpecifyItem* GetSolePathItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  return spec->specify_items[0];
}

// path_declaration ::= state_dependent_path_declaration ; (ifnone)
TEST(ParserA702, PathDeclStateDependentIfnone) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
}

// § module_path_conditional_expression used in specify ifnone
TEST(ParserA83, ModulePathConditionalInSpecify) {
  auto r = Parse(
      "module m(input a, input en, output y);\n"
      "  specify\n"
      "    if (en) (a => y) = 2;\n"
      "    ifnone (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
