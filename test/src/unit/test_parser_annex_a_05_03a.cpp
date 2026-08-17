#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// A.5.3's udp_body and the productions under it that give a table its entries:
// combinational_body and combinational_entry, sequential_body with and without
// an initial statement, udp_initial_statement and init_val, sequential_entry,
// and the input lists -- seq_input_list, level_input_list, edge_input_list and
// edge_indicator.
//
// test/src/unit/test_parser_annex_a_05_03b.cpp holds the rest of A.5.3: the
// symbols a field may hold, and the positions its BNF does not admit each in.
// The two files share the suite UdpBodyGrammar because they cover one
// production set, and they are two files because the one they were in reached
// the 1000-line maximum assert-no-oversized-source-files fails at.

TEST(UdpBodyGrammar, UdpBody_CombinationalAlternative) {
  auto r = Parse(
      "primitive and_gate(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  EXPECT_EQ(udp->table.size(), 4);
}

TEST(UdpBodyGrammar, UdpBody_SequentialAlternative) {
  auto r = Parse(
      "primitive latch(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->table.size(), 3);
}

TEST(UdpBodyGrammar, CombBody_SingleEntry) {
  auto r = Parse(
      "primitive buf_prim(output y, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  EXPECT_EQ(udp->table.size(), 1);
}

TEST(UdpBodyGrammar, CombBody_MultipleEntries) {
  auto r = Parse(
      "primitive xor_gate(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->table.size(), 4);
}

TEST(UdpBodyGrammar, UdpBody_SimCombinational) {
  auto r = Parse(
      "primitive or_gate(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  EXPECT_EQ(eval.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(eval.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(eval.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(eval.Evaluate({'1', '1'}), '1');
}

TEST(UdpBodyGrammar, CombBody_SimFirstMatch) {
  auto r = Parse(
      "primitive nand_gate(output y, input a, b);\n"
      "  table\n"
      "    0 ? : 1;\n"
      "    ? 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  EXPECT_EQ(eval.Evaluate({'0', '0'}), '1');
  EXPECT_EQ(eval.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(eval.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(eval.Evaluate({'1', '1'}), '0');
}

TEST(UdpBodyGrammar, CombEntry_MultiInput) {
  auto r = Parse(
      "primitive three_in(output y, input a, b, c);\n"
      "  table\n"
      "    0 0 0 : 0;\n"
      "    1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 2);
  EXPECT_EQ(udp->table[0].inputs.size(), 3);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], '0');
  EXPECT_EQ(udp->table[0].inputs[2], '0');
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[1].inputs[0], '1');
  EXPECT_EQ(udp->table[1].inputs[1], '1');
  EXPECT_EQ(udp->table[1].inputs[2], '1');
  EXPECT_EQ(udp->table[1].output, '1');
}

TEST(UdpBodyGrammar, CombEntry_Structure) {
  auto r = Parse(
      "primitive buf_prim(output y, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 2);

  EXPECT_EQ(udp->table[0].inputs.size(), 1);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[0].current_state, 0);

  EXPECT_EQ(udp->table[1].inputs[0], '1');
  EXPECT_EQ(udp->table[1].output, '1');
}

TEST(UdpBodyGrammar, SeqBody_WithInitial) {
  auto r = Parse(
      "primitive latch_init(output reg q, input d, en);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
  EXPECT_EQ(udp->table.size(), 3);
}

TEST(UdpBodyGrammar, SeqBody_WithoutInitial) {
  auto r = Parse(
      "primitive latch_noinit(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    1 1 : ? : 1;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_FALSE(udp->has_initial);
  EXPECT_EQ(udp->table.size(), 3);
}

TEST(UdpBodyGrammar, UdpBody_SimSequential) {
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
  UdpEvalState eval(*udp);

  eval.Evaluate({'0', '1'});
  EXPECT_EQ(eval.GetOutput(), '0');

  eval.Evaluate({'1', '0'});
  EXPECT_EQ(eval.GetOutput(), '0');
}

TEST(UdpBodyGrammar, InitVal_1b0) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '0');
}

TEST(UdpBodyGrammar, InitVal_1b1) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '1');
}

TEST(UdpBodyGrammar, InitVal_1bx) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(UdpBodyGrammar, InitVal_1bX) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'bX;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(UdpBodyGrammar, InitVal_1B0) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'B0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '0');
}

TEST(UdpBodyGrammar, InitVal_1B1) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'B1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '1');
}

TEST(UdpBodyGrammar, InitVal_1Bx) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'Bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(UdpBodyGrammar, InitVal_1BX) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1'BX;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, 'x');
}

TEST(UdpBodyGrammar, InitVal_Bare0) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '0');
}

TEST(UdpBodyGrammar, InitVal_Bare1) {
  auto r = Parse(
      "primitive p(output reg q, input d, clk);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->initial_value, '1');
}

TEST(UdpBodyGrammar, SeqEntry_ThreeFields) {
  auto r = Parse(
      "primitive srff(output reg q, input s, r);\n"
      "  table\n"
      "    1 0 : 0 : 1;\n"
      "    0 1 : 1 : 0;\n"
      "    0 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table.size(), 3);

  EXPECT_EQ(udp->table[0].inputs[0], '1');
  EXPECT_EQ(udp->table[0].inputs[1], '0');
  EXPECT_EQ(udp->table[0].current_state, '0');
  EXPECT_EQ(udp->table[0].output, '1');

  EXPECT_EQ(udp->table[1].current_state, '1');
  EXPECT_EQ(udp->table[1].output, '0');

  EXPECT_EQ(udp->table[2].current_state, '?');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(UdpBodyGrammar, MixedLevelEdgeSensitive) {
  auto r = Parse(
      "primitive jk_edge_ff(output reg q, input clock, j, k, preset, clear);\n"
      "  table\n"
      "    ? ? ? 0 1 : ? : 1;\n"
      "    ? ? ? 1 0 : ? : 0;\n"
      "    r 0 0 0 0 : 0 : 1;\n"
      "    r 0 0 1 1 : ? : -;\n"
      "    f ? ? ? ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 5);

  EXPECT_EQ(udp->table[0].inputs[0], '?');
  EXPECT_EQ(udp->table[0].output, '1');
  EXPECT_EQ(udp->table[2].inputs[0], 'r');
  EXPECT_EQ(udp->table[2].output, '1');
  EXPECT_EQ(udp->table[4].inputs[0], 'f');
  EXPECT_EQ(udp->table[4].output, '-');
}

TEST(UdpBodyGrammar, SeqInputList_WithEdge) {
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

  EXPECT_EQ(udp->table[0].inputs[1], 'r');
  EXPECT_EQ(udp->table[2].inputs[1], 'f');
}

TEST(UdpBodyGrammar, SeqInputList_LevelOnly) {
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

  for (const auto& row : udp->table) {
    for (char c : row.inputs) {
      EXPECT_TRUE(c == '0' || c == '1' || c == '?' || c == 'x' || c == 'b');
    }
  }
}

TEST(UdpBodyGrammar, LevelInputList_Single) {
  auto r = Parse(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->table[0].inputs.size(), 1);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
}

TEST(UdpBodyGrammar, LevelInputList_Multiple) {
  auto r = Parse(
      "primitive four_in(output y, input a, b, c, d);\n"
      "  table\n"
      "    0 1 0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table[0].inputs.size(), 4);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], '1');
  EXPECT_EQ(udp->table[0].inputs[2], '0');
  EXPECT_EQ(udp->table[0].inputs[3], '1');
}

TEST(UdpBodyGrammar, EdgeInputList_LeadingLevel) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];

  ASSERT_EQ(udp->table[0].inputs.size(), 2);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
}

TEST(UdpBodyGrammar, EdgeInputList_TrailingLevel) {
  auto r = Parse(
      "primitive clk_first(output reg q, input clk, d);\n"
      "  table\n"
      "    r 0 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table[0].inputs.size(), 2);
  EXPECT_EQ(udp->table[0].inputs[0], 'r');
  EXPECT_EQ(udp->table[0].inputs[1], '0');
}

TEST(UdpBodyGrammar, EdgeInputList_SurroundedByLevels) {
  auto r = Parse(
      "primitive three_in(output reg q, input a, clk, b);\n"
      "  table\n"
      "    0 r 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table[0].inputs.size(), 3);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
  EXPECT_EQ(udp->table[0].inputs[2], '1');
}

TEST(UdpBodyGrammar, EdgeIndicator_EdgeSymbol) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
}

TEST(UdpBodyGrammar, EdgeIndicator_Paren01) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 (01) : ? : 0;\n"
      "    1 (01) : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  ASSERT_EQ(udp->table[0].inputs.size(), 2);
}

TEST(UdpBodyGrammar, EdgeIndicator_SimParen01) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 (01) : ? : 0;\n"
      "    1 (01) : ? : 1;\n"
      "    ? (10) : ? : -;\n"
      "    ? (0x) : ? : -;\n"
      "    ? (x1) : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  UdpEvalState eval(*udp);
  EXPECT_EQ(eval.GetOutput(), '0');

  eval.SetInputs({'1', '0'});
  EXPECT_EQ(eval.EvaluateWithEdge({'1', '1'}, 1, '0'), '1');

  EXPECT_EQ(eval.EvaluateWithEdge({'1', '0'}, 1, '1'), '1');

  eval.SetInputs({'0', '0'});
  EXPECT_EQ(eval.EvaluateWithEdge({'0', '1'}, 1, '0'), '0');
}
}  // namespace
