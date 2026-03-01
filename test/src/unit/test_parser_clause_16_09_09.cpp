// §16.9.9: Conditions over sequences

#include "fixture_parser.h"

using namespace delta;

namespace {

// sequence_expr ::= expression_or_dist throughout sequence_expr
TEST(ParserA210, SequenceExpr_Throughout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    en throughout (a ##1 b ##1 c));\n"
              "endmodule\n"));
}

using VerifyParseTest = ProgramTestParse;

// Assert property with throughout operator.
TEST(ParserSection16, Sec16_5_1_SequenceThroughout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) !burst throughout (##2 trdy[*7]));\n"
              "endmodule\n"));
}

// --- Test helpers ---
struct ParseResult16b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16b Parse(const std::string& src) {
  ParseResult16b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §16.9.4 Sequence throughout
// =============================================================================
TEST(ParserSection16, SequenceThroughoutBasic) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) !burst_mode throughout (##2 trdy[*7]));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
