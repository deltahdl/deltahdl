// §16.9.3: Sampled value functions

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

// =============================================================================
// §16.9 -- System functions for assertions ($sampled, $rose, $fell, $stable)
// =============================================================================
TEST(ParserSection16, SampledFunctionInAssert) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    else $error(\"a=%b b=%b\", $sampled(a), $sampled(b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, RoseFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $rose(req) |-> ##[1:3] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, FellFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $fell(req) |-> ##1 !ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, StableFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $stable(data) |-> valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, PastFunctionWithTicks) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $past(req, 2) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection16, ChangedFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $changed(data) |-> valid);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
