// §9.4.2.4: Sequence events

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection9c, SequenceEventParenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s1;\n"
              "    @(posedge clk) a ##1 b;\n"
              "  endsequence\n"
              "  initial begin\n"
              "    @(s1) $display(\"matched\");\n"
              "  end\n"
              "endmodule\n"));
}

struct ParseResult9c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9c Parse(const std::string& src) {
  ParseResult9c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §9.4.2.4 -- Sequence events
// =============================================================================
TEST(ParserSection9b, SequenceEventInEventControl) {
  auto r = Parse(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial @(abc) $display(\"match\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
