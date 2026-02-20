#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/udp_eval.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

}  // namespace

// =============================================================================
// A.5.3 -- UDP body
//
// udp_body ::= combinational_body | sequential_body
// combinational_body ::= table combinational_entry { combinational_entry }
//                         endtable
// combinational_entry ::= level_input_list : output_symbol ;
// sequential_body ::= [ udp_initial_statement ] table sequential_entry
//                     { sequential_entry } endtable
// udp_initial_statement ::= initial output_port_identifier = init_val ;
// init_val ::= 1'b0 | 1'b1 | 1'bx | 1'bX | 1'B0 | 1'B1 | 1'Bx | 1'BX
//              | 1 | 0
// sequential_entry ::= seq_input_list : current_state : next_state ;
// seq_input_list ::= level_input_list | edge_input_list
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
// Production 1: udp_body ::= combinational_body | sequential_body
// ---------------------------------------------------------------------------

// udp_body alternative 1: combinational_body
TEST(ParserAnnexA053, UdpBody_CombinationalAlternative) {
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

// udp_body alternative 2: sequential_body
TEST(ParserAnnexA053, UdpBody_SequentialAlternative) {
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

// Simulation: combinational body evaluates correctly
TEST(ParserAnnexA053, UdpBody_SimCombinational) {
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

// ---------------------------------------------------------------------------
// Production 2: combinational_body ::= table combinational_entry
//               { combinational_entry } endtable
// ---------------------------------------------------------------------------

// Single combinational entry
TEST(ParserAnnexA053, CombBody_SingleEntry) {
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

// Multiple combinational entries
TEST(ParserAnnexA053, CombBody_MultipleEntries) {
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

// Simulation: verify table entries are evaluated in order
TEST(ParserAnnexA053, CombBody_SimFirstMatch) {
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

// ---------------------------------------------------------------------------
// Production 3: combinational_entry ::= level_input_list : output_symbol ;
// ---------------------------------------------------------------------------

// Verify structure of a parsed combinational entry
TEST(ParserAnnexA053, CombEntry_Structure) {
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
  // Row 0: input '0', output '0'
  EXPECT_EQ(udp->table[0].inputs.size(), 1);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[0].current_state, 0);
  // Row 1: input '1', output '1'
  EXPECT_EQ(udp->table[1].inputs[0], '1');
  EXPECT_EQ(udp->table[1].output, '1');
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

// Sequential body with initial statement
TEST(ParserAnnexA053, SeqBody_WithInitial) {
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

// Simulation: initial value is used at construction
TEST(ParserAnnexA053, SeqBody_SimInitialValue) {
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
  // Initial value is 1
  EXPECT_EQ(eval.GetOutput(), '1');
  // Enable low -> no change -> stays at 1
  eval.Evaluate({'0', '0'});
  EXPECT_EQ(eval.GetOutput(), '1');
}

// Simulation: sequential body evaluates correctly
TEST(ParserAnnexA053, UdpBody_SimSequential) {
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
  // Enable high, data=0 -> output=0
  eval.Evaluate({'0', '1'});
  EXPECT_EQ(eval.GetOutput(), '0');
  // Enable low -> no change
  eval.Evaluate({'1', '0'});
  EXPECT_EQ(eval.GetOutput(), '0');
}

// ---------------------------------------------------------------------------
// Production 5: udp_initial_statement ::= initial output_port_identifier =
//               init_val ;
// ---------------------------------------------------------------------------

// Initial statement parsed correctly
TEST(ParserAnnexA053, InitStmt_Parsed) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

// Initial statement with value 1
TEST(ParserAnnexA053, InitStmt_ValueOne) {
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

// ---------------------------------------------------------------------------
// Production 6: init_val ::= 1'b0 | 1'b1 | 1'bx | 1'bX | 1'B0 | 1'B1 |
//               1'Bx | 1'BX | 1 | 0
// ---------------------------------------------------------------------------

// init_val = 1'b0
TEST(ParserAnnexA053, InitVal_1b0) {
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

// init_val = 1'b1
TEST(ParserAnnexA053, InitVal_1b1) {
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

// init_val = 1'bx
TEST(ParserAnnexA053, InitVal_1bx) {
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

// init_val = 1'bX (uppercase)
TEST(ParserAnnexA053, InitVal_1bX) {
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

// init_val = 1'B0 (uppercase B)
TEST(ParserAnnexA053, InitVal_1B0) {
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

// init_val = 1'B1 (uppercase B)
TEST(ParserAnnexA053, InitVal_1B1) {
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

// init_val = 1'Bx (uppercase B, lowercase x)
TEST(ParserAnnexA053, InitVal_1Bx) {
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

// init_val = 1'BX (uppercase B, uppercase X)
TEST(ParserAnnexA053, InitVal_1BX) {
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

// init_val = bare 0
TEST(ParserAnnexA053, InitVal_Bare0) {
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

// init_val = bare 1
TEST(ParserAnnexA053, InitVal_Bare1) {
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

// ---------------------------------------------------------------------------
// Production 8: seq_input_list ::= level_input_list | edge_input_list
// ---------------------------------------------------------------------------

// seq_input_list as level_input_list (no edge symbols)
TEST(ParserAnnexA053, SeqInputList_LevelOnly) {
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
  // All entries use only level symbols
  for (const auto& row : udp->table) {
    for (char c : row.inputs) {
      EXPECT_TRUE(c == '0' || c == '1' || c == '?' || c == 'x' || c == 'b');
    }
  }
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

// ---------------------------------------------------------------------------
// Production 10: edge_input_list ::= { level_symbol } edge_indicator
//                { level_symbol }
// ---------------------------------------------------------------------------

// Edge indicator with leading level symbol
TEST(ParserAnnexA053, EdgeInputList_LeadingLevel) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  auto* udp = r.cu->udps[0];
  // d='0' (level), clk='r' (edge)
  ASSERT_EQ(udp->table[0].inputs.size(), 2);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
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

// ---------------------------------------------------------------------------
// Production 11: edge_indicator ::= ( level_symbol level_symbol ) |
//                edge_symbol
// ---------------------------------------------------------------------------

// edge_indicator as edge_symbol
TEST(ParserAnnexA053, EdgeIndicator_EdgeSymbol) {
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

// Simulation: parenthesized edge (01) behaves as rising edge
TEST(ParserAnnexA053, EdgeIndicator_SimParen01) {
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
  // Rising edge with d=1 -> output=1
  eval.SetInputs({'1', '0'});
  EXPECT_EQ(eval.EvaluateWithEdge({'1', '1'}, 1, '0'), '1');
  // Falling edge -> no change
  EXPECT_EQ(eval.EvaluateWithEdge({'1', '0'}, 1, '1'), '1');
  // Rising edge with d=0 -> output=0
  eval.SetInputs({'0', '0'});
  EXPECT_EQ(eval.EvaluateWithEdge({'0', '1'}, 1, '0'), '0');
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

// next_state as output_symbol '1'
TEST(ParserAnnexA053, NextState_One) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    1 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].output, '1');
}

// next_state as output_symbol 'x'
TEST(ParserAnnexA053, NextState_X) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    1 1 : ? : x;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].output, 'x');
}

// next_state as '-' (no change)
TEST(ParserAnnexA053, NextState_Dash) {
  auto r = Parse(
      "primitive p(output reg q, input d, en);\n"
      "  table\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->udps[0]->table[0].output, '-');
}

// Simulation: '-' keeps current output
TEST(ParserAnnexA053, NextState_SimDashKeepsState) {
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
  // Initial output = 1
  EXPECT_EQ(eval.GetOutput(), '1');
  // Enable low -> no change -> still 1
  eval.Evaluate({'0', '0'});
  EXPECT_EQ(eval.GetOutput(), '1');
  // Enable high, data=0 -> output=0
  eval.Evaluate({'0', '1'});
  EXPECT_EQ(eval.GetOutput(), '0');
  // Enable low -> no change -> still 0
  eval.Evaluate({'1', '0'});
  EXPECT_EQ(eval.GetOutput(), '0');
}

// ---------------------------------------------------------------------------
// Production 14: output_symbol ::= 0 | 1 | x | X
// ---------------------------------------------------------------------------

// All four output_symbol values in combinational entries
TEST(ParserAnnexA053, OutputSymbol_AllFour) {
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
  // 'X' is stored as-is by UdpCharFromToken (first char)
  EXPECT_TRUE(udp->table[3].output == 'X' || udp->table[3].output == 'x');
}

// Simulation: output_symbol values
TEST(ParserAnnexA053, OutputSymbol_SimValues) {
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
  // Unmatched -> x
  EXPECT_EQ(eval.Evaluate({'x'}), 'x');
}

// ---------------------------------------------------------------------------
// Production 15: level_symbol ::= 0 | 1 | x | X | ? | b | B
// ---------------------------------------------------------------------------

// All level symbols in input positions
TEST(ParserAnnexA053, LevelSymbol_AllValues) {
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

// Simulation: '?' matches 0, 1, and x
TEST(ParserAnnexA053, LevelSymbol_SimQuestion) {
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

// Simulation: 'b' matches 0 and 1, but not x
TEST(ParserAnnexA053, LevelSymbol_SimB) {
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
  // 'b' does not match 'x'
  EXPECT_EQ(eval.Evaluate({'x'}), 'x');
}

// ---------------------------------------------------------------------------
// Production 16: edge_symbol ::= r | R | f | F | p | P | n | N | *
// ---------------------------------------------------------------------------

// All edge symbols parsed
TEST(ParserAnnexA053, EdgeSymbol_AllValues) {
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

// Simulation: 'r' matches rising edge (0->1)
TEST(ParserAnnexA053, EdgeSymbol_SimR) {
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
  // Rising edge (0->1) with d=1 -> output=1
  EXPECT_EQ(eval.EvaluateWithEdge({'1', '1'}, 1, '0'), '1');
}

// Simulation: 'f' matches falling edge (1->0)
TEST(ParserAnnexA053, EdgeSymbol_SimF) {
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
  // Falling edge (1->0) with dash -> no change
  EXPECT_EQ(eval.EvaluateWithEdge({'1', '0'}, 1, '1'), '1');
}

// Simulation: 'p' matches positive edge (0->1, 0->x, x->1)
TEST(ParserAnnexA053, EdgeSymbol_SimP) {
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
  // 0->1 matches p
  eval.SetInputs({'0'});
  EXPECT_EQ(eval.EvaluateWithEdge({'1'}, 0, '0'), '1');
}

// Simulation: 'n' matches negative edge (1->0, 1->x, x->0)
TEST(ParserAnnexA053, EdgeSymbol_SimN) {
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
  // 1->0 matches n
  eval.SetInputs({'1'});
  EXPECT_EQ(eval.EvaluateWithEdge({'0'}, 0, '1'), '0');
}

// Simulation: '*' matches any change
TEST(ParserAnnexA053, EdgeSymbol_SimStar) {
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
  // 0->1 matches *
  eval.SetInputs({'0'});
  EXPECT_EQ(eval.EvaluateWithEdge({'1'}, 0, '0'), '1');
  // 1->0 also matches *
  EXPECT_EQ(eval.EvaluateWithEdge({'0'}, 0, '1'), '1');
}
