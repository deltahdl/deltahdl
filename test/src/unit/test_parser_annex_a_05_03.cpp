// Annex A.5.3: UDP body

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A5UdpSequential) {
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

// Combinational entry with multi-input level_input_list
TEST(ParserAnnexA053, CombEntry_MultiInput) {
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

// Sequential body with single entry
TEST(ParserAnnexA053, SeqBody_SingleEntry) {
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

// seq_input_list as edge_input_list (contains edge symbol)
TEST(ParserAnnexA053, SeqInputList_WithEdge) {
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
  // Row 0: 'd' is level, 'clk' is edge
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
  EXPECT_EQ(udp->table[2].inputs[1], 'f');
}

// Multiple level symbols in input list
TEST(ParserAnnexA053, LevelInputList_Multiple) {
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

// Edge indicator with trailing level symbol
TEST(ParserAnnexA053, EdgeInputList_TrailingLevel) {
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

// Edge indicator surrounded by level symbols (3 inputs)
TEST(ParserAnnexA053, EdgeInputList_SurroundedByLevels) {
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

// edge_indicator as parenthesized form (01)
TEST(ParserAnnexA053, EdgeIndicator_Paren01) {
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
  // Parenthesized (01) should produce exactly 2 input entries per row
  ASSERT_EQ(udp->table[0].inputs.size(), 2);
}

// edge_indicator as parenthesized form (10)
TEST(ParserAnnexA053, EdgeIndicator_Paren10) {
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

// edge_indicator as parenthesized form (0x)
TEST(ParserAnnexA053, EdgeIndicator_Paren0x) {
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

// edge_indicator as parenthesized form (x1)
TEST(ParserAnnexA053, EdgeIndicator_Parenx1) {
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

// ---------------------------------------------------------------------------
// Production 12: current_state ::= level_symbol
// ---------------------------------------------------------------------------
// current_state as '0'
TEST(ParserAnnexA053, CurrentState_Zero) {
  auto r = Parse(
      "primitive p(output reg q, input s, r);\n"
      "  table\n"
      "    1 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, '0');
}

// current_state as '1'
TEST(ParserAnnexA053, CurrentState_One) {
  auto r = Parse(
      "primitive p(output reg q, input s, r);\n"
      "  table\n"
      "    0 1 : 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, '1');
}

// current_state as '?'
TEST(ParserAnnexA053, CurrentState_Question) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, '?');
}

// current_state as 'x'
TEST(ParserAnnexA053, CurrentState_X) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : x : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, 'x');
}

// current_state as 'b'
TEST(ParserAnnexA053, CurrentState_B) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : b : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].current_state, 'b');
}

// ---------------------------------------------------------------------------
// Production 13: next_state ::= output_symbol | -
// ---------------------------------------------------------------------------
// next_state as output_symbol '0'
TEST(ParserAnnexA053, NextState_Zero) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].output, '0');
}

}  // namespace
