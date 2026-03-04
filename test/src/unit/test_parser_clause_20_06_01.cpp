// §20.6.1: Type name function

#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

struct ParseResult6b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6b Parse(const std::string& src) {
  ParseResult6b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// §20.6 — Bare type keyword in expression context ($typename(logic))
TEST(ParserSection6, BareTypeKeywordInExpr) {
  auto r = Parse(
      "module t;\n"
      "  initial $display($typename(logic));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
