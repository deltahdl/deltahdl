// §6.20.7: $ as a constant

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary — $
TEST(ParserA84, PrimaryDollar) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

// =============================================================================
// LRM section 20.6.3 -- $isunbounded (range system function)
// =============================================================================
TEST(ParserSection20, IsUnboundedBasic) {
  auto r = Parse(
      "module m #(parameter int P = $);\n"
      "  initial begin\n"
      "    if ($isunbounded(P)) $display(\"unbounded\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
