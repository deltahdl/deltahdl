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
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
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
// A.5.3 -- UDP body (part a: productions 1-8)
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
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
  auto *udp = r.cu->udps[0];
  // All entries use only level symbols
  for (const auto &row : udp->table) {
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
  auto *udp = r.cu->udps[0];
  // Row 0: 'd' is level, 'clk' is edge
  EXPECT_EQ(udp->table[0].inputs[1], 'r');
  EXPECT_EQ(udp->table[2].inputs[1], 'f');
}
