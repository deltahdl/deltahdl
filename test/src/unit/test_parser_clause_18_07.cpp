// §18.7: Inline constraints—randomize() with

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult19 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult19 Parse(const std::string& src) {
  ParseResult19 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

TEST(ParserSection18, RandomizeWithMultipleConstraints) {
  auto r = Parse(
      "class SimpleSum;\n"
      "  rand bit [7:0] x, y, z;\n"
      "  constraint c { z == x + y; }\n"
      "  function void test();\n"
      "    this.randomize() with { x < y; x > 10; y < 200; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, RandomizeWithRestrictedIdList) {
  auto r = Parse(
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "function int F(int y);\n"
      "  C obj;\n"
      "  F = obj.randomize() with (x) { x < y; };\n"
      "endfunction\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserA82, RandomizeCallWithConstraintBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize() with { x < 10; }; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
