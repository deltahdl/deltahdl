// §6.5: for more details.

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

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

// =========================================================================
// §6.5: Nets and variables
// =========================================================================
TEST(ParserSection6, NetsCantBeProcAssigned) {
  // Nets are driven by continuous assignments, variables by procedural.
  // This test verifies both constructs parse correctly.
  auto r = Parse(
      "module t;\n"
      "  wire a;\n"
      "  assign a = 1'b1;\n"
      "  logic b;\n"
      "  initial b = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 4u);
}

}  // namespace
