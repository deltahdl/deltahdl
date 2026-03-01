// §16.7: Sequences

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// §A.2.10 Production #26: sequence_expr — many alternatives
// =============================================================================
// sequence_expr ::= cycle_delay_range sequence_expr ...
TEST(ParserA210, SequenceExpr_CycleDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##2 a);\n"
              "endmodule\n"));
}

// sequence_expr ::= sequence_expr cycle_delay_range sequence_expr ...
TEST(ParserA210, SequenceExpr_Concatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b ##2 c);\n"
              "endmodule\n"));
}

// sequence_expr ::= clocking_event sequence_expr
TEST(ParserA210, SequenceExpr_ClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a |-> @(negedge clk) b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #27: cycle_delay_range
// cycle_delay_range ::=
//     ## constant_primary
//   | ## [ cycle_delay_const_range_expression ]
//   | ##[*]
//   | ##[+]
// =============================================================================
TEST(ParserA210, CycleDelayRange_Constant) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:5] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_OpenEndRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:$] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Star) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##[*] a);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Plus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##[+] a);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Zero) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##0 b);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #39: cycle_delay_const_range_expression
// cycle_delay_const_range_expression ::=
//     constant_expression : constant_expression
//   | constant_expression : $
// =============================================================================
TEST(ParserA210, CycleDelayConstRange_FiniteRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[2:5] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayConstRange_OpenEnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:$] b);\n"
              "endmodule\n"));
}

// sequence_list_of_arguments — mixed positional + named
TEST(ParserA210, SequenceListOfArguments_Mixed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b, c); a ##1 b ##1 c; endsequence\n"
              "  assert property (@(posedge clk) s(x, .b(y), .c(z)));\n"
              "endmodule\n"));
}

// sequence_expr ::= ( sequence_expr {, sequence_match_item} ) [sequence_abbrev]
TEST(ParserA210, SequenceExpr_ParenWithMatchItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

using VerifyParseTest = ProgramTestParse;

// =============================================================================
// Section 16.5.1 -- Sequence operators in concurrent assertions
// =============================================================================
// Assert property with ## cycle delay operator.
TEST(ParserSection16, Sec16_5_1_SequenceDelayOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req ##1 gnt ##1 !req);\n"
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
// §16.7 Sequences — concatenation and delay
// =============================================================================
TEST(ParserSection16, SequenceConcatDelay1) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##1 gnt ##1 !req);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceConcatDelay2) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##2 gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceDelayRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##[4:32] gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
