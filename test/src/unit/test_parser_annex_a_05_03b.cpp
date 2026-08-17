#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// A.5.3's symbol productions: current_state, next_state, output_symbol,
// level_symbol and edge_symbol, and after them the cases asserting a symbol
// rejected in a position its BNF does not admit it in.
//
// test/src/unit/test_parser_annex_a_05_03a.cpp holds the rest of A.5.3:
// udp_body and the productions that give a table its entries. Its head says why
// the coverage of one production set is in two files.
TEST(UdpBodyGrammar, CurrentState_X) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : x : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, 'x');
}

TEST(UdpBodyGrammar, CurrentState_B) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : b : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, 'b');
}

TEST(UdpBodyGrammar, SequentialCurrentStateField) {
  auto r = Parse(
      "primitive srff(output reg q, input s, r);\n"
      "  table\n"
      "    1 0 : 0 : 1;\n"
      "    1 0 : 1 : 1;\n"
      "    0 1 : ? : 0;\n"
      "    0 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 4);

  EXPECT_EQ(udp->table[0].current_state, '0');
  EXPECT_EQ(udp->table[0].output, '1');

  EXPECT_EQ(udp->table[1].current_state, '1');
  EXPECT_EQ(udp->table[1].output, '1');

  EXPECT_EQ(udp->table[2].current_state, '?');
  EXPECT_EQ(udp->table[2].output, '0');

  EXPECT_EQ(udp->table[3].current_state, '?');
  EXPECT_EQ(udp->table[3].output, '-');
}

TEST(UdpBodyGrammar, NextState_SimDashKeepsState) {
  auto r = Parse(
      "primitive latch(output reg q, input d, en);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);

  EXPECT_EQ(eval.GetOutput(), '1');

  eval.Evaluate({'0', '0'});
  EXPECT_EQ(eval.GetOutput(), '1');

  eval.Evaluate({'0', '1'});
  EXPECT_EQ(eval.GetOutput(), '0');

  eval.Evaluate({'1', '0'});
  EXPECT_EQ(eval.GetOutput(), '0');
}

TEST(UdpBodyGrammar, OutputSymbol_AllFour) {
  auto r = Parse(
      "primitive p(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : x;\n"
      "    1 1 : X;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 4);
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[1].output, '1');
  EXPECT_EQ(udp->table[2].output, 'x');

  EXPECT_TRUE(udp->table[3].output == 'X' || udp->table[3].output == 'x');
}

TEST(UdpBodyGrammar, OutputSymbol_SimValues) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  EXPECT_EQ(eval.Evaluate({'0'}), '0');
  EXPECT_EQ(eval.Evaluate({'1'}), '1');

  EXPECT_EQ(eval.Evaluate({'x'}), 'x');
}

TEST(UdpBodyGrammar, LevelSymbol_AllValues) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "    x : x;\n"
      "    X : x;\n"
      "    ? : 0;\n"
      "    b : 0;\n"
      "    B : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 7);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[1].inputs[0], '1');
  EXPECT_EQ(udp->table[2].inputs[0], 'x');
  EXPECT_TRUE(udp->table[3].inputs[0] == 'X' || udp->table[3].inputs[0] == 'x');
  EXPECT_EQ(udp->table[4].inputs[0], '?');
  EXPECT_EQ(udp->table[5].inputs[0], 'b');
  EXPECT_TRUE(udp->table[6].inputs[0] == 'B' || udp->table[6].inputs[0] == 'b');
}

TEST(UdpBodyGrammar, LevelSymbol_SimQuestion) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  EXPECT_EQ(eval.Evaluate({'0'}), '1');
  EXPECT_EQ(eval.Evaluate({'1'}), '1');
  EXPECT_EQ(eval.Evaluate({'x'}), '1');
}

TEST(UdpBodyGrammar, LevelSymbol_SimB) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    b : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  EXPECT_EQ(eval.Evaluate({'0'}), '1');
  EXPECT_EQ(eval.Evaluate({'1'}), '1');

  EXPECT_EQ(eval.Evaluate({'x'}), 'x');
}

TEST(UdpBodyGrammar, EdgeSymbol_AllValues) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    r : ? : 1;\n"
      "    R : ? : 1;\n"
      "    f : ? : 0;\n"
      "    F : ? : 0;\n"
      "    p : ? : 1;\n"
      "    P : ? : 1;\n"
      "    n : ? : 0;\n"
      "    N : ? : 0;\n"
      "    * : ? : x;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 9);
  EXPECT_EQ(udp->table[0].inputs[0], 'r');
  EXPECT_TRUE(udp->table[1].inputs[0] == 'R' || udp->table[1].inputs[0] == 'r');
  EXPECT_EQ(udp->table[2].inputs[0], 'f');
  EXPECT_TRUE(udp->table[3].inputs[0] == 'F' || udp->table[3].inputs[0] == 'f');
  EXPECT_EQ(udp->table[4].inputs[0], 'p');
  EXPECT_TRUE(udp->table[5].inputs[0] == 'P' || udp->table[5].inputs[0] == 'p');
  EXPECT_EQ(udp->table[6].inputs[0], 'n');
  EXPECT_TRUE(udp->table[7].inputs[0] == 'N' || udp->table[7].inputs[0] == 'n');
  EXPECT_EQ(udp->table[8].inputs[0], '*');
}

TEST(UdpBodyGrammar, EdgeSymbol_SimR) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    1 r : ? : 1;\n"
      "    0 r : ? : 0;\n"
      "    ? f : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  eval.SetInputs({'1', '0'});

  EXPECT_EQ(eval.EvaluateWithEdge({'1', '1'}, 1, '0'), '1');
}

TEST(UdpBodyGrammar, EdgeSymbol_SimF) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    1 r : ? : 1;\n"
      "    0 r : ? : 0;\n"
      "    ? f : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  eval.SetInputs({'1', '0'});
  eval.EvaluateWithEdge({'1', '1'}, 1, '0');
  EXPECT_EQ(eval.GetOutput(), '1');

  EXPECT_EQ(eval.EvaluateWithEdge({'1', '0'}, 1, '1'), '1');
}

TEST(UdpBodyGrammar, EdgeSymbol_SimP) {
  auto r = Parse(
      "primitive p_udp(output reg q, input a);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    p : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);

  eval.SetInputs({'0'});
  EXPECT_EQ(eval.EvaluateWithEdge({'1'}, 0, '0'), '1');
}

TEST(UdpBodyGrammar, EdgeSymbol_SimN) {
  auto r = Parse(
      "primitive n_udp(output reg q, input a);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    n : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);

  eval.SetInputs({'1'});
  EXPECT_EQ(eval.EvaluateWithEdge({'0'}, 0, '1'), '0');
}

TEST(UdpBodyGrammar, EdgeSymbol_SimStar) {
  auto r = Parse(
      "primitive star_udp(output reg q, input a);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    * : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);

  eval.SetInputs({'0'});
  EXPECT_EQ(eval.EvaluateWithEdge({'1'}, 0, '0'), '1');

  EXPECT_EQ(eval.EvaluateWithEdge({'0'}, 0, '1'), '1');
}

TEST(UdpBodyGrammar, EmptyTableError) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "  endtable\n"
      "endprimitive\n");
  // §29.3.4 owns the table entries; A.5.3 only states the udp_body production.
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table shall contain at least one entry", 3, "29.3.4"));
}

TEST(UdpBodyGrammar, SeqEntry_ManyInputsWithEdge) {
  auto r = Parse(
      "primitive p(output reg q, input a, b, c, d);\n"
      "  table\n"
      "    0 0 0 r : ? : 1;\n"
      "    1 1 1 f : ? : 0;\n"
      "    ? ? ? ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 3u);
  EXPECT_EQ(udp->table[0].inputs.size(), 4u);
  EXPECT_EQ(udp->table[0].inputs[3], 'r');
  EXPECT_EQ(udp->table[1].inputs[3], 'f');
}

TEST(UdpBodyGrammar, SeqBody_SingleEntryMinimal) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->table.size(), 1u);
  EXPECT_EQ(udp->table[0].current_state, '0');
  EXPECT_EQ(udp->table[0].output, '1');
}

TEST(UdpBodyGrammar, NextState_AllValuesInOneUdp) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    0 : 0 : 0;\n"
      "    0 : 1 : 1;\n"
      "    1 : 0 : x;\n"
      "    1 : 1 : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 4u);
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[1].output, '1');
  EXPECT_EQ(udp->table[2].output, 'x');
  EXPECT_EQ(udp->table[3].output, '-');
}

// Error/edge cases for the symbol-position restrictions that §A.5.3's BNF
// imposes. Each parses a table that violates one production and expects the
// parser to flag it, observing the grammar rule being enforced.

// combinational_entry's output is an output_symbol (0 1 x X); a level-only
// symbol such as b is not a legal combinational output.
TEST(UdpBodyGrammar, CombinationalOutputRejectsNonOutputSymbol) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : b;\n"
      "  endtable\n"
      "endprimitive\n");
  // §29.3.6 owns the symbol tables A.5.3 names; the report is filed there.
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output field shall be 0, 1, or x (- is sequential only)", 3,
      "29.3.6"));
}

// The dash (no-change) is only legal as a next_state; a combinational
// output_symbol may not be a dash.
TEST(UdpBodyGrammar, CombinationalOutputRejectsDash) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : -;\n"
      "  endtable\n"
      "endprimitive\n");
  // §29.3.6 owns the symbol tables A.5.3 names; the report is filed there.
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output field shall be 0, 1, or x (- is sequential only)", 3,
      "29.3.6"));
}

// current_state is a level_symbol, so an edge symbol is not allowed there.
TEST(UdpBodyGrammar, CurrentStateRejectsEdgeSymbol) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : r : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  // §29.3.6 owns the symbol tables A.5.3 names; the report is filed there.
  EXPECT_TRUE(ReportedError(
      r.diags, "edge symbols shall not appear in the current-state field", 3,
      "29.3.6"));
}

// current_state is a level_symbol; the dash (no-change) is not a level_symbol.
TEST(UdpBodyGrammar, CurrentStateRejectsDash) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : - : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  // §29.3.6 owns the symbol tables A.5.3 names; the report is filed there.
  EXPECT_TRUE(ReportedError(
      r.diags, "- shall not appear in the current-state field", 3, "29.3.6"));
}

// Input fields are made of level/edge symbols; the dash is neither and may not
// appear in the input list.
TEST(UdpBodyGrammar, InputFieldRejectsDash) {
  auto r = Parse(
      "primitive p(output y, input a, b);\n"
      "  table\n"
      "    - 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  // §29.3.6 owns the symbol tables A.5.3 names; the report is filed there.
  EXPECT_TRUE(ReportedError(r.diags, "- shall not appear in a UDP input field",
                            3, "29.3.6"));
}

// A parenthesized edge_indicator's two endpoints are level_symbols; an edge
// symbol inside the parentheses is not permitted.
TEST(UdpBodyGrammar, ParenEdgeEndpointsRejectNonLevelSymbol) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  table\n"
      "    0 (r0) : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  // §29.3.6 owns the symbol tables A.5.3 names; the report is filed there.
  EXPECT_TRUE(ReportedError(
      r.diags, "parenthesized edge endpoints shall be level symbols", 3,
      "29.3.6"));
}

}  // namespace
