#include "fixture_parser.h"
#include "fixture_program.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpDeclGrammar, TableEdgeSymbols) {
  auto r = Parse(
      "primitive edge_det(output reg q, input d, input clk);\n"
      "  table\n"
      "    ? f : ? : 1;\n"
      "    ? p : ? : 0;\n"
      "    * ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 3u);
  EXPECT_EQ(udp->table[0].inputs[1], 'f');
  EXPECT_EQ(udp->table[1].inputs[1], 'p');
  EXPECT_EQ(udp->table[2].inputs[0], '*');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(UdpDeclGrammar, TableWildcardSymbols) {
  auto r = Parse(
      "primitive wild(output out, input a, input b);\n"
      "  table\n"
      "    ? ? : 0;\n"
      "    b b : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 2u);
  EXPECT_EQ(udp->table[0].inputs[0], '?');
  EXPECT_EQ(udp->table[0].inputs[1], '?');
  EXPECT_EQ(udp->table[1].inputs[0], 'b');
  EXPECT_EQ(udp->table[1].inputs[1], 'b');
}

TEST(UdpDeclGrammar, SimCombinationalWildcard) {
  auto r = Parse(
      "primitive mux(output out, input a, b, sel);\n"
      "  table\n"
      "    0 ? 0 : 0;\n"
      "    1 ? 0 : 1;\n"
      "    ? 0 1 : 0;\n"
      "    ? 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1', '1'}), '1');
}

TEST(UdpBodyGrammar, NextState_Dash) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].output, '-');
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

TEST(UserDefinedPrimitiveParsing, UdpTableSpecialChars) {
  auto r = Parse(
      "primitive edge_detect(output reg q, input d, clk);\n"
      "  table\n"
      "    ? f : ? : 1;\n"
      "    ? p : ? : 0;\n"
      "    * ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 3);

  struct Check {
    size_t row;
    size_t col;
    char val;
  };
  Check input_checks[] = {{0, 1, 'f'}, {1, 1, 'p'}, {2, 0, '*'}};
  for (const auto& c : input_checks) {
    EXPECT_EQ(udp->table[c.row].inputs[c.col], c.val);
  }
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(UserDefinedPrimitiveParsing, TableSymbol0And1) {
  auto r = Parse(
      "primitive and_gate(output out, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 4);

  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], '0');
  EXPECT_EQ(udp->table[0].output, '0');

  EXPECT_EQ(udp->table[3].inputs[0], '1');
  EXPECT_EQ(udp->table[3].inputs[1], '1');
  EXPECT_EQ(udp->table[3].output, '1');
}

TEST(UserDefinedPrimitiveParsing, TableSymbolQuestionMark) {
  auto r = Parse(
      "primitive buf_udp(output out, input in);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "    ? : x;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  ASSERT_EQ(r.cu->udps[0]->table.size(), 3);

  EXPECT_EQ(r.cu->udps[0]->table[2].inputs[0], '?');
  EXPECT_EQ(r.cu->udps[0]->table[2].output, 'x');
}

TEST(UserDefinedPrimitiveParsing, TableSymbolX) {
  auto r = Parse(
      "primitive xor_udp(output out, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 0;\n"
      "    x ? : x;\n"
      "    ? x : x;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 6);

  EXPECT_EQ(udp->table[4].inputs[0], 'x');
  EXPECT_EQ(udp->table[4].inputs[1], '?');
  EXPECT_EQ(udp->table[4].output, 'x');
}

TEST(UserDefinedPrimitiveParsing, TableSymbolB) {
  auto r = Parse(
      "primitive or_udp(output out, input a, b);\n"
      "  table\n"
      "    b 0 : 0;\n"
      "    0 b : 0;\n"
      "    1 ? : 1;\n"
      "    ? 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 4);
  EXPECT_EQ(udp->table[0].inputs[0], 'b');
  EXPECT_EQ(udp->table[1].inputs[1], 'b');
}

TEST(UserDefinedPrimitiveParsing, TableSymbolDashNoChange) {
  auto r = Parse(
      "primitive latch(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 3);

  EXPECT_EQ(udp->table[2].output, '-');

  EXPECT_EQ(udp->table[2].current_state, '?');
}

TEST(UserDefinedPrimitiveParsing, TableEdgeSymbolsRAndF) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "    ? f : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 3);
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
  EXPECT_EQ(udp->table[1].inputs[1], 'r');
  EXPECT_EQ(udp->table[2].inputs[1], 'f');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(UserDefinedPrimitiveParsing, TableEdgeSymbolStar) {
  auto r = Parse(
      "primitive any_change(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "    * ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 3);
  EXPECT_EQ(udp->table[2].inputs[0], '*');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(UserDefinedPrimitiveParsing, TableEdgeSymbolsPAndN) {
  EXPECT_TRUE(
      ParseOk("primitive pos_neg(output reg q, input d, clk);\n"
              "  table\n"
              "    0 p : ? : 0;\n"
              "    1 p : ? : 1;\n"
              "    ? n : ? : -;\n"
              "  endtable\n"
              "endprimitive\n"));
}

TEST(UserDefinedPrimitiveParsing, TableEdgeNotationParenthesized) {
  EXPECT_TRUE(
      ParseOk("primitive edge_udp(output reg q, input d, clk);\n"
              "  table\n"
              "    0 (01) : ? : 0;\n"
              "    1 (01) : ? : 1;\n"
              "    ? (10) : ? : -;\n"
              "    ? (0x) : ? : -;\n"
              "    ? (x1) : ? : -;\n"
              "  endtable\n"
              "endprimitive\n"));
}

}  // namespace
