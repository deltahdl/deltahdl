// §18.11.1: Inline constraint checker

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

// =============================================================================
// §18.7 Inline constraints -- randomize() with (additional)
// =============================================================================
TEST(ParserSection18, RandomizeWithNullArg) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  function void test();\n"
      "    this.randomize(null) with { x > 0; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserA82, RandomizeCallWithNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(null); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
