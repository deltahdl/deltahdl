// §19.4: Using covergroups in classes

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA211, CovergroupDecl_InClass) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  covergroup cg;\n"
              "  endgroup\n"
              "endclass\n"));
}

struct ParseResult8b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult8b Parse(const std::string& src) {
  ParseResult8b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// §8.3 — Covergroup inside class
TEST(ParserSection8, CovergroupInClass) {
  auto r = Parse(
      "class CoveredClass;\n"
      "  int x;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

}  // namespace
