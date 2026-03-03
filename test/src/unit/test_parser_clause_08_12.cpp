// §8.12: Assignment, renaming, and copying

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA24, ClassNewCopy) {
  // new expression (shallow copy)
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c1, c2;\n"
      "  initial c2 = new c1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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

// §8.12 — Shallow copy with new
TEST(ParserSection8, ShallowCopy) {
  auto r = Parse(
      "module m;\n"
      "  class Packet;\n"
      "    int data;\n"
      "  endclass\n"
      "  initial begin\n"
      "    Packet p1, p2;\n"
      "    p1 = new;\n"
      "    p2 = new p1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
