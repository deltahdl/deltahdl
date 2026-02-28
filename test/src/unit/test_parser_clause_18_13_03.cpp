// §18.13.3: srandom()

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
// §18.13.3 srandom() -- random stability and process
// =============================================================================
TEST(ParserSection18, SrandomMethodCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void seed_it();\n"
      "    this.srandom(42);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, SrandomInInitialBlock) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.srandom(123);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection18, SrandomWithExpression) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void seed_it(int seed_val);\n"
      "    this.srandom(seed_val + 1);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

}  // namespace
