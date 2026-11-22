#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

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
      "    0 : x;\n"
      "    1 : x;\n"
      "    x : x;\n"
      "    X : x;\n"
      "    ? : x;\n"
      "    b : x;\n"
      "    B : x;\n"
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
      "    r : ? : -;\n"
      "    R : ? : -;\n"
      "    f : ? : -;\n"
      "    F : ? : -;\n"
      "    p : ? : -;\n"
      "    P : ? : -;\n"
      "    n : ? : -;\n"
      "    N : ? : -;\n"
      "    * : ? : -;\n"
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

TEST(UdpBodyGrammar, CombinationalOutputRejectsNonOutputSymbol) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : b;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output field shall be 0, 1, or x (- is sequential only)", 3,
      "29.3.6"));
}

TEST(UdpBodyGrammar, CombinationalOutputRejectsDash) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : -;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP output field shall be 0, 1, or x (- is sequential only)", 3,
      "29.3.6"));
}

TEST(UdpBodyGrammar, CurrentStateRejectsEdgeSymbol) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : r : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "edge symbols shall not appear in the current-state field", 3,
      "29.3.6"));
}

TEST(UdpBodyGrammar, CurrentStateRejectsDash) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : - : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "- shall not appear in the current-state field", 3, "29.3.6"));
}

TEST(UdpBodyGrammar, InputFieldRejectsDash) {
  auto r = Parse(
      "primitive p(output y, input a, b);\n"
      "  table\n"
      "    - 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "- shall not appear in a UDP input field",
                            3, "29.3.6"));
}

TEST(UdpBodyGrammar, ParenEdgeEndpointsRejectNonLevelSymbol) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  table\n"
      "    0 (r0) : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "parenthesized edge endpoints shall be level symbols", 3,
      "29.3.6"));
}

TEST(UdpBodyGrammar, InputSymbolOutsideLevelAndEdgeIsRejected) {
  auto r = Parse(
      "primitive p(output q, input a, b);\n"
      "  table\n"
      "    2 0 : 0;\n"
      "    a 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a UDP input field is a level_symbol (0, 1, x, X, ?, b, B)", 3,
      "A.5.3"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a UDP input field is a level_symbol (0, 1, x, X, ?, b, B)", 4,
      "A.5.3"));
  EXPECT_FALSE(
      ReportedError(r.diags, "UDP table row has 1 input field", 3, "29.3.4"));
}

TEST(UdpBodyGrammar, InputSymbolRunIsEveryCharacter) {
  auto r = Parse(
      "primitive p(output q, input a, b);\n"
      "  table\n"
      "    01 : 0;\n"
      "    x1 : 1;\n"
      "    1b : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps[0]->table.size(), 3u);
  ASSERT_EQ(r.cu->udps[0]->table[0].inputs.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->table[0].inputs[0], '0');
  EXPECT_EQ(r.cu->udps[0]->table[0].inputs[1], '1');
  ASSERT_EQ(r.cu->udps[0]->table[1].inputs.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->table[1].inputs[0], 'x');
  ASSERT_EQ(r.cu->udps[0]->table[2].inputs.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->table[2].inputs[1], 'b');
}

TEST(UdpBodyGrammar, StateAndOutputFieldsAreOneSymbolEach) {
  auto r = Parse(
      "primitive p(output reg q, input a);\n"
      "  table\n"
      "    0 : 01 : 1;\n"
      "    1 : 0 : 10;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a UDP entry's state and output fields are one symbol each", 3,
      "A.5.3"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a UDP entry's state and output fields are one symbol each", 4,
      "A.5.3"));
}

std::string SequentialRow(const std::string& row) {
  return "primitive p(output reg q, input c, input d);\n"
         "  table\n"
         "    " +
         row +
         "\n"
         "  endtable\n"
         "endprimitive\n";
}

void ExpectRowReported(const std::string& row, const char* message,
                       const char* subclause) {
  EXPECT_TRUE(
      ReportedError(Parse(SequentialRow(row)).diags, message, 3, subclause))
      << row;
}

TEST(UdpSymbolFields, ADashOrASingleSymbolInAParenthesisedEdgeIsRejected) {
  for (const char* row : {"(0-) 0 : 0 : 1;", "(-1) 0 : 0 : 1;"}) {
    ExpectRowReported(
        row, "parenthesized edge endpoints shall be level symbols", "29.3.6");
  }
  ExpectRowReported("(0) 0 : 0 : 1;",
                    "an edge in parentheses is two level symbols", "29.3");
}

TEST(UdpSymbolFields, UpperCaseLevelSymbolsAsEdgeEndpointsAreAccepted) {
  EXPECT_TRUE(ParseOk(SequentialRow("(XB) 0 : 0 : 1;")));
}

TEST(UdpSymbolFields, ADashInASequentialInputFieldIsRejected) {
  ExpectRowReported("- 0 : 0 : 1;", "- shall not appear in a UDP input field",
                    "29.3.6");
}

TEST(UdpSymbolFields, UpperCaseLevelSymbolsInTheCurrentStateAreAccepted) {
  for (const char* row : {"0 0 : X : 1;", "0 0 : B : 1;"}) {
    EXPECT_TRUE(ParseOk(SequentialRow(row))) << row;
  }
}

TEST(UdpSymbolFields, AStarInTheCurrentStateIsRejected) {
  ExpectRowReported("0 0 : * : 1;",
                    "edge symbols shall not appear in the current-state field",
                    "29.3.6");
}

TEST(UdpSymbolFields, DISABLED_AParenthesisedEdgeInTheStateOrOutputIsRejected) {
  for (const char* row : {"0 0 : (01) : 1;", "0 0 : 0 : (01);"}) {
    ExpectRowReported(row, "an edge indicator stands only among the inputs",
                      "A.5.3");
  }
}

TEST(UdpSymbolFields, AnUpperCaseXInTheNextStateIsAccepted) {
  EXPECT_TRUE(ParseOk(SequentialRow("0 0 : 0 : X;")));
}

TEST(UdpSymbolFields, ANonOutputSymbolInTheNextStateIsRejected) {
  for (const char* row : {"0 0 : 0 : ?;", "0 0 : 0 : b;", "0 0 : 0 : r;"}) {
    ExpectRowReported(row, "UDP output field shall be 0, 1, or x", "29.3.6");
  }
}

TEST(UdpSymbolFields, AnEdgeLetterInACombinationalOutputIsRejected) {
  auto r = Parse(
      "primitive p(output q, input a);\n"
      "  table\n"
      "    0 : r;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "UDP output field shall be 0, 1, or x", 3,
                            "29.3.6"));
}

TEST(UdpSymbolFields, TwoEdgesInOneRowAreRejectedInEveryNotation) {
  for (const char* row : {"(01)(01) : 0 : 1;", "(01) r : 0 : 1;",
                          "n (10) : 0 : 1;", "* p : ? : 1;"}) {
    ExpectRowReported(row,
                      "UDP table row shall contain at most one input "
                      "transition",
                      "29.3.4");
  }
}

TEST(UdpSymbolFields, TwoEdgesInARowOfANonAnsiUdpAreRejected) {
  auto r = Parse(
      "primitive p(q, c, d);\n"
      "  output q; reg q; input c, d;\n"
      "  table\n"
      "    (01)(01) : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row shall contain at most one input transition", 4,
      "29.3.4"));
}

TEST(UdpSymbolFields, OneEdgeAmongLevelsIsAcceptedInEitherNotation) {
  for (const char* row : {"(01) 0 : 0 : 1;", "0 r : 0 : 1;"}) {
    EXPECT_TRUE(ParseOk(SequentialRow(row))) << row;
  }
}

std::string TwoInputUdp(const std::string& output, const std::string& rows) {
  return "primitive p(output " + output +
         "q, input a, input b);\n"
         "  table\n" +
         rows +
         "  endtable\n"
         "endprimitive\n";
}

TEST(UdpStateTable, ACombinationalOutputOfTwoSymbolsIsRejected) {
  EXPECT_TRUE(ReportedError(Parse(TwoInputUdp("", "    0 0 : 01;\n")).diags,
                            "a UDP entry's state and output fields are one "
                            "symbol each",
                            3, "A.5.3"));
}

TEST(UdpStateTable, AThreeFieldEntryInACombinationalTableIsRejected) {
  const char* odd = "    1 ? : 0 : 1;\n";
  const char* even = "    0 0 : 0;\n    0 1 : 1;\n";
  auto first = Parse(TwoInputUdp("", std::string(odd) + even));
  EXPECT_TRUE(ReportedError(first.diags,
                            "sequential UDP shall declare its output port reg",
                            3, "29.3.2"));
  auto last = Parse(TwoInputUdp("", std::string(even) + odd));
  EXPECT_TRUE(ReportedError(last.diags,
                            "sequential UDP shall declare its output port reg",
                            5, "29.3.2"));
  EXPECT_TRUE(ParseOk(TwoInputUdp("", std::string(even) + "    1 ? : 0;\n")));
}

TEST(UdpStateTable, ATwoFieldEntryInASequentialTableIsRejected) {
  const char* odd = "    0 0 : 1;\n";
  const char* latch = "    0 1 : ? : 1;\n    1 ? : ? : 0;\n";
  auto first = Parse(TwoInputUdp("reg ", std::string(odd) + latch));
  EXPECT_TRUE(ReportedError(
      first.diags, "combinational UDP shall not declare its output port reg", 3,
      "29.3.2"));
  auto last = Parse(TwoInputUdp("reg ", std::string(latch) + odd));
  EXPECT_TRUE(ReportedError(
      last.diags, "combinational UDP shall not declare its output port reg", 5,
      "29.3.2"));
  EXPECT_TRUE(ParseOk(TwoInputUdp("reg ", latch)));
}

TEST(UdpStateTable, AnEmptySequentialTableIsRejected) {
  EXPECT_TRUE(ReportedError(Parse(TwoInputUdp("reg ", "")).diags,
                            "UDP table shall contain at least one entry", 3,
                            "29.3.4"));
  auto r = Parse(
      "primitive p(output reg q, input a, input b);\n"
      "  initial q = 0;\n"
      "  table\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table shall contain at least one entry", 4, "29.3.4"));
}

TEST(UdpStateTable, ASequentialEntryWithoutItsSemicolonIsRejected) {
  auto r = Parse(TwoInputUdp("reg ", "    r 0 : ? : 0\n    f 1 : ? : 1;\n"));
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got identifier", 4, "29.3.4"));
}

TEST(UdpStateTable, ACurrentStateNotSetOffByAColonIsRejected) {
  EXPECT_TRUE(ReportedError(
      Parse(TwoInputUdp("reg ", "    0 0 ? : 0;\n")).diags,
      "UDP table row has 3 input field(s) but primitive 'p' declares 2 input "
      "port(s)",
      3, "29.3.4"));
  EXPECT_TRUE(ParseOk(TwoInputUdp("reg ", "    0 1 : ? : 1;\n")));
}

}  // namespace
