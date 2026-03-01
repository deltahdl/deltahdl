// §20.6.3: Range system function

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult21 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult21 Parse(const std::string& src) {
  ParseResult21 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

TEST(ParserSection20, IsUnboundedInConditional) {
  auto r = Parse(
      "module m #(parameter int N = $);\n"
      "  generate\n"
      "    if (!$isunbounded(N)) begin\n"
      "      assign out = in;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection20, IsUnboundedWithBoundedParam) {
  auto r = Parse(
      "module m #(parameter int P = 42);\n"
      "  initial begin\n"
      "    if ($isunbounded(P)) $display(\"yes\");\n"
      "    else $display(\"no\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
