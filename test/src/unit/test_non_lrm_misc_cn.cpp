// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

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

namespace {

TEST(ParserSection16, MulticlockSequenceDeclTwo) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_multi;\n"
      "    @(posedge clk1) a ##1 @(posedge clk2) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.14.7 -- Inferred clocking and disable functions
// =============================================================================
TEST(ParserSection16, InferredClockInProperty) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p_inferred(clk_ev = $inferred_clock);\n"
      "    @clk_ev a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, InferredDisableInProperty) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "  property p_dis(rst_cond = $inferred_disable);\n"
      "    disable iff (rst_cond) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, InferredClockAndDisableTogether) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(negedge clk); endclocking\n"
      "  default disable iff rst;\n"
      "  property p_both(c = $inferred_clock, d = $inferred_disable);\n"
      "    @c disable iff (d) req |-> ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §16.9.4 -- Sequence throughout (additional tests)
// =============================================================================
TEST(ParserSection16, SequenceThroughoutWithImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) req |-> en throughout (##2 ack[*3]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
