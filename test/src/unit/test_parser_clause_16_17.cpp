// §16.17: Expect statement

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// §A.2.10 Production #2: concurrent_assertion_statement
// concurrent_assertion_statement ::=
//     assert_property_statement | assume_property_statement
//   | cover_property_statement  | cover_sequence_statement
//   | restrict_property_statement
// =============================================================================
// Productions #3-#5 tested above (assert/assume/cover property).
// =============================================================================
// §A.2.10 Production #6: expect_property_statement
// expect_property_statement ::= expect ( property_spec ) action_block
// =============================================================================
TEST(ParserA210, ExpectPropertyStatement) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    expect (a |-> b) $display(\"pass\"); else $display(\"fail\");\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserA210, ExpectPropertyStatement_NoActions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    expect (req |-> ack);\n"
              "  end\n"
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

TEST(ParserSection16, ExpectStatement) {
  auto r = Parse(
      "module top();\n"
      "  logic clk, a, b;\n"
      "  initial begin\n"
      "    expect (@(posedge clk) a ##1 b);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
