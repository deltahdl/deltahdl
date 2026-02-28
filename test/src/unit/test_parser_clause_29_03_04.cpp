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

using SpecifyParseTest = ProgramTestParse;

// =============================================================================
// Parser test fixture
// =============================================================================
struct SpecifyTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  // Helper: get first specify block from first module.
  ModuleItem* FirstSpecifyBlock(CompilationUnit* cu) {
    for (auto* item : cu->modules[0]->items) {
      if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
    }
    return nullptr;
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

struct ParseResult30 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult30 Parse(const std::string& src) {
  ParseResult30 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection29, SequentialCurrentStateField) {
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
  // First row: current state '0', output '1'
  EXPECT_EQ(udp->table[0].current_state, '0');
  EXPECT_EQ(udp->table[0].output, '1');
  // Second row: current state '1', output '1'
  EXPECT_EQ(udp->table[1].current_state, '1');
  EXPECT_EQ(udp->table[1].output, '1');
  // Third row: current state '?'
  EXPECT_EQ(udp->table[2].current_state, '?');
  EXPECT_EQ(udp->table[2].output, '0');
  // Fourth row: no-change
  EXPECT_EQ(udp->table[3].current_state, '?');
  EXPECT_EQ(udp->table[3].output, '-');
}

static void VerifyUdpRowInputs(const UdpTableRow& row,
                               const std::string& expected) {
  ASSERT_EQ(row.inputs.size(), expected.size());
  for (size_t j = 0; j < expected.size(); ++j) {
    EXPECT_EQ(row.inputs[j], expected[j]);
  }
}

struct SeqUdpRow {
  std::string inputs;
  char state;
  char output;
};

static void VerifySeqUdpTable(const UdpDecl* udp, const SeqUdpRow expected[],
                              size_t count) {
  ASSERT_EQ(udp->table.size(), count);
  for (size_t i = 0; i < count; ++i) {
    VerifyUdpRowInputs(udp->table[i], expected[i].inputs);
    EXPECT_EQ(udp->table[i].current_state, expected[i].state);
    EXPECT_EQ(udp->table[i].output, expected[i].output);
  }
}

TEST(ParserSection29, SequentialUdp) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  SeqUdpRow expected[] = {{"0r", '?', '0'}, {"1r", '?', '1'}};
  VerifySeqUdpTable(udp, expected, std::size(expected));
}

}  // namespace
