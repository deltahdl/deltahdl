#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- udp_body ---

TEST(UdpBodyGrammar, UdpSequential) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0 ;\n"
      "    1 r : ? : 1 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
}

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

// --- combinational_body ---

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

// --- combinational_entry ---

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

// --- sequential_body ---

TEST(UdpBodyGrammar, SeqBody_SingleEntry) {
  auto r = Parse(
      "primitive sr_min(output reg q, input s, r);\n"
      "  table\n"
      "    1 0 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->table.size(), 1);
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

TEST(UdpBodyGrammar, SeqBody_SimInitialValue) {
  auto r = Parse(
      "primitive latch_init(output reg q, input d, en);\n"
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
}

// --- udp_initial_statement / init_val ---

TEST(UdpBodyGrammar, InitStmt_ValueOne) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
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

// --- sequential_entry ---

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

// --- seq_input_list ---

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

// --- level_input_list ---

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

// --- edge_input_list ---

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

// --- edge_indicator ---

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

TEST(UdpBodyGrammar, EdgeIndicator_Paren10) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    ? (10) : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table[0].inputs.size(), 2);
}

TEST(UdpBodyGrammar, EdgeIndicator_Paren0x) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    ? (0x) : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->table[0].inputs.size(), 2);
}

TEST(UdpBodyGrammar, EdgeIndicator_Parenx1) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    ? (x1) : ? : -;\n"
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

TEST(UdpBodyGrammar, TableEdgeNotationParenthesized) {
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

// --- current_state ---

TEST(UdpBodyGrammar, CurrentState_Zero) {
  auto r = Parse(
      "primitive p(output reg q, input s, r);\n"
      "  table\n"
      "    1 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, '0');
}

TEST(UdpBodyGrammar, CurrentState_One) {
  auto r = Parse(
      "primitive p(output reg q, input s, r);\n"
      "  table\n"
      "    0 1 : 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, '1');
}

TEST(UdpBodyGrammar, CurrentState_Question) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, '?');
}

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

// --- next_state ---

TEST(UdpBodyGrammar, NextState_Zero) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].output, '0');
}

TEST(UdpBodyGrammar, NextState_One) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].output, '1');
}

TEST(UdpBodyGrammar, NextState_X) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    1 1 : ? : x;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].output, 'x');
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

// --- output_symbol ---

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

// --- level_symbol ---

TEST(UdpBodyGrammar, LevelSymbol_AllValues) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "    x : 0;\n"
      "    X : 0;\n"
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

TEST(UdpBodyGrammar, TableSymbol0And1) {
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

TEST(UdpBodyGrammar, TableSymbolQuestionMark) {
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

TEST(UdpBodyGrammar, TableSymbolX) {
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

TEST(UdpBodyGrammar, TableSymbolB) {
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

TEST(UdpBodyGrammar, TableSymbolDashNoChange) {
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

// --- edge_symbol ---

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

TEST(UdpBodyGrammar, TableEdgeSymbolsRAndF) {
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

TEST(UdpBodyGrammar, TableEdgeSymbolStar) {
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

TEST(UdpBodyGrammar, TableEdgeSymbolsPAndN) {
  EXPECT_TRUE(
      ParseOk("primitive pos_neg(output reg q, input d, clk);\n"
              "  table\n"
              "    0 p : ? : 0;\n"
              "    1 p : ? : 1;\n"
              "    ? n : ? : -;\n"
              "  endtable\n"
              "endprimitive\n"));
}

}  // namespace
