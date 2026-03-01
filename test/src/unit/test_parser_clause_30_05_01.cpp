// §30.5.1: Specifying transition delays on module paths

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using ConfigParseTest = ProgramTestParse;

namespace {

TEST(ParserSection28, Sec28_12_SpecparamMinTypMax) {
  EXPECT_TRUE(
      ParseOk("module m(input a, output b);\n"
              "  specify\n"
              "    specparam tPLH = 3:5:7;\n"
              "    (a => b) = tPLH;\n"
              "  endspecify\n"
              "endmodule\n"));
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

TEST_F(SpecifyTest, PathDelayWithRiseFall) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = (3, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto& delays = spec->specify_items[0]->path.delays;
  EXPECT_EQ(delays.size(), 2u);
}

TEST_F(SpecifyTest, PathDelayThreeValues) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = (2, 3, 4);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items[0]->path.delays.size(), 3u);
}

TEST(ParserSection28, Sec28_12_TwoDelayPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (5, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  EXPECT_EQ(sp.sole_item->kind, SpecifyItemKind::kPathDecl);
  ASSERT_EQ(sp.sole_item->path.delays.size(), 2u);
}

TEST(ParserSection28, Sec28_12_ThreeDelayPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (3, 7, 11);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  ASSERT_EQ(sp.sole_item->path.delays.size(), 3u);
}

TEST(ParserSection28, Sec28_12_SixDelayPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  ASSERT_EQ(sp.sole_item->path.delays.size(), 6u);
}

}  // namespace
