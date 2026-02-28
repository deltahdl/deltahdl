// §29.3.4: UDP state table

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- Unmatched inputs produce x ---
TEST(ParserAnnexA051, SimUnmatchedInputsX) {
  auto r = Parse(
      "primitive partial(output out, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '0'}), 'x');
}

// ---------------------------------------------------------------------------
// Production 4: sequential_body ::= [ udp_initial_statement ] table
//               sequential_entry { sequential_entry } endtable
// ---------------------------------------------------------------------------
// Sequential body without initial statement
TEST(ParserAnnexA053, SeqBody_WithoutInitial) {
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

// ---------------------------------------------------------------------------
// Production 7: sequential_entry ::= seq_input_list : current_state :
//               next_state ;
// ---------------------------------------------------------------------------
// Verify the three-field structure of a sequential entry
TEST(ParserAnnexA053, SeqEntry_ThreeFields) {
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
  // Row 0: inputs [1,0], current_state '0', next_state '1'
  EXPECT_EQ(udp->table[0].inputs[0], '1');
  EXPECT_EQ(udp->table[0].inputs[1], '0');
  EXPECT_EQ(udp->table[0].current_state, '0');
  EXPECT_EQ(udp->table[0].output, '1');
  // Row 1: inputs [0,1], current_state '1', next_state '0'
  EXPECT_EQ(udp->table[1].current_state, '1');
  EXPECT_EQ(udp->table[1].output, '0');
  // Row 2: inputs [0,0], current_state '?', next_state '-'
  EXPECT_EQ(udp->table[2].current_state, '?');
  EXPECT_EQ(udp->table[2].output, '-');
}

// =============================================================================
// A.5.3 -- UDP body (part b: productions 9-16)
//
// level_input_list ::= level_symbol { level_symbol }
// edge_input_list ::= { level_symbol } edge_indicator { level_symbol }
// edge_indicator ::= ( level_symbol level_symbol ) | edge_symbol
// current_state ::= level_symbol
// next_state ::= output_symbol | -
// output_symbol ::= 0 | 1 | x | X
// level_symbol ::= 0 | 1 | x | X | ? | b | B
// edge_symbol ::= r | R | f | F | p | P | n | N | *
// =============================================================================
// ---------------------------------------------------------------------------
// Production 9: level_input_list ::= level_symbol { level_symbol }
// ---------------------------------------------------------------------------
// Single level symbol input list
TEST(ParserAnnexA053, LevelInputList_Single) {
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

}  // namespace
