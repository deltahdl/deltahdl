#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UdpStateTable, MissingTableKeywordRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  0 : 1;\n"
      "  1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  // TokenKindName answers "token" for every keyword, so the sentence names the
  // row's first token rather than the missing `table`.
  EXPECT_TRUE(ReportedError(r.diags, "expected token, got integer literal", 2,
                            "29.3.4"));
}

TEST(UdpStateTable, MissingEndtableKeywordRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n");
  // The source ends after line 4's newline, so the EOF token the `endtable`
  // expectation reports against stands at line 5, column 1.
  EXPECT_TRUE(ReportedError(r.diags, "expected token, got EOF", 5, "29.3.4"));
}

TEST(UdpStateTable, RowMissingSemicolonRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 1\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  // The row's missing `;` is reported against the first token of the next row.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got integer literal", 4, "29.3.4"));
}

TEST(UdpStateTable, InputFieldOrderFollowsHeaderPortList) {
  auto r = Parse(
      "primitive gate(output y, input a, input b, input c);\n"
      "  table\n"
      "    0 1 0 : 0;\n"
      "    1 0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
  ASSERT_EQ(udp->table.size(), 2u);
  ASSERT_EQ(udp->table[0].inputs.size(), 3u);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], '1');
  EXPECT_EQ(udp->table[0].inputs[2], '0');
}

TEST(UdpStateTable, InputFieldOrderIgnoresPortDeclarationOrder) {
  // §29.3.4: a row's input fields follow the header port-list order, which is
  // independent of the order the input ports are declared. Here the port list
  // is (q, a, b, c) but the declarations appear as c, b, a; the table fields
  // must still bind to a, b, c.
  auto r = Parse(
      "primitive gate(q, a, b, c);\n"
      "  output q;\n"
      "  input c;\n"
      "  input b;\n"
      "  input a;\n"
      "  table\n"
      "    0 1 0 : 0;\n"
      "    1 0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
}

TEST(UdpStateTable, CombinationalRowHasInputsAndOutputOnly) {
  auto r = Parse(
      "primitive and2(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 2u);
  EXPECT_EQ(udp->table[0].inputs.size(), 2u);
  EXPECT_EQ(udp->table[0].current_state, 0);
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[1].output, '1');
}

TEST(UdpStateTable, SequentialRowHasInputsCurrentStateAndOutput) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : 1 : 0;\n"
      "    1 r : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 2u);
  EXPECT_EQ(udp->table[0].inputs.size(), 2u);
  EXPECT_EQ(udp->table[0].current_state, '1');
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[1].current_state, '0');
  EXPECT_EQ(udp->table[1].output, '1');
}

TEST(UdpStateTable, AllXInputsWithZeroOutputRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x x : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row with all-x inputs shall specify x output", 3,
      "29.3.4"));
}

TEST(UdpStateTable, AllXInputsWithOneOutputRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    x : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row with all-x inputs shall specify x output", 3,
      "29.3.4"));
}

TEST(UdpStateTable, AllXInputsWithXOutputAccepted) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x x : x;\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, DuplicateInputsWithDifferentOutputsRejected) {
  auto r = Parse(
      "primitive bad(output y, input a, input b);\n"
      "  table\n"
      "    0 1 : 0;\n"
      "    0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  // Parser::ValidateUdpTable compares whole rows once the table is complete,
  // so the report stands at the primitive's own line rather than at a row.
  EXPECT_TRUE(ReportedError(r.diags,
                            "UDP table rows with identical inputs shall not "
                            "specify different outputs",
                            1, "29.3.4"));
}

TEST(UdpStateTable, SequentialDuplicateInputsWithDifferentOutputsRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input d, input en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    0 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "UDP table rows with identical inputs shall not "
                            "specify different outputs",
                            1, "29.3.4"));
}

TEST(UdpStateTable, RowWithTwoInputTransitionsRejected) {
  // §29.3.4 permits at most one input transition per row; the LRM gives
  // "(01) (10) 0 : 0 : 1 ;" as an illegal example because two fields change.
  auto r = Parse(
      "primitive seq(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01) (10) 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row shall contain at most one input transition", 3,
      "29.3.4"));
}

TEST(UdpStateTable, RowWithSingleInputTransitionAccepted) {
  auto r = Parse(
      "primitive seq(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01) 0 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, IdenticalDuplicateRowsNotFlagged) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, RowWithTwoShorthandEdgesRejected) {
  // §29.3.4 caps a row at one input transition however the edge is spelled.
  // Here both transitions use the shorthand letter form (r, f) instead of the
  // parenthesized (vw) form, so the row still names two transitions and is
  // rejected on the same at-most-one-transition rule.
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    r f : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row shall contain at most one input transition", 3,
      "29.3.4"));
}

TEST(UdpStateTable, SequentialAllXInputsWithXOutputAccepted) {
  // The all-x-inputs rule also governs sequential rows, which carry an extra
  // current-state field between the inputs and the output. An all-x input row
  // whose output is x is well formed.
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    x x : 0 : x;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, SequentialAllXInputsWithNonXOutputRejected) {
  // Same sequential row shape, but the output is 1 while every input field is
  // x; the all-x rule requires the output to be x, so this is rejected.
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    x x : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row with all-x inputs shall specify x output", 3,
      "29.3.4"));
}

TEST(UdpStateTable, DuplicateEdgeInputsWithDifferentOutputsRejected) {
  // The duplicate-row rule compares the whole input combination "including
  // edges". Two rows sharing the same rising-edge transition and level inputs
  // but naming different outputs collide and are rejected.
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    (01) 0 : 0 : 0;\n"
      "    (01) 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "UDP table rows with identical inputs shall not "
                            "specify different outputs",
                            1, "29.3.4"));
}

TEST(UdpStateTable, DuplicateEdgeRowsWithSameOutputNotFlagged) {
  // Counterpart to the edge-collision case: rows with an identical edge
  // combination that also agree on the output are consistent, so the
  // duplicate-row rule does not fire. This shows the collision above is driven
  // by the differing output, not merely by the repeated edge.
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    (01) 0 : 0 : 0;\n"
      "    (01) 0 : 0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, AllXInputsWithOneOutputNames29_3_4) {
  // §29.3.4: "If all input values are specified as x, then the output state
  // shall be specified as x." The report names that subclause, so a case can
  // tell this rejection from the several other rules a UDP table row breaks in
  // the same way -- a row of the wrong width, a row holding z, a row whose
  // output symbol is illegal. has_errors is the same value for all of them.
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x x : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row with all-x inputs shall specify x output", 3,
      "29.3.4"));
}

// The pair for the case above. §29.3.4, Syntax 29-1: every table_entry ends
// with a semicolon, and this row omits it, so the run is rejected by
// Parser::Expect rather than by one of parser_udp.cpp's own reports. The
// sentence it writes, `expected ';', got integer literal`, names no rule; the
// subclause puts the token-level rejection and the rule-level one above on the
// same clause of the standard.
TEST(UdpStateTable, MalformedRowNames29_3_4) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 1\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';'", 4, "29.3.4"));
}

}  // namespace
