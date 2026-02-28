// §29.3.6: Summary of symbols

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// --- udp_declaration: table row with edge symbols ---
TEST(ParserAnnexA051, TableEdgeSymbols) {
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

// --- udp_declaration: table with wildcard symbols ---
TEST(ParserAnnexA051, TableWildcardSymbols) {
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

// --- Combinational UDP with wildcard matching in simulation ---
TEST(ParserAnnexA051, SimCombinationalWildcard) {
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

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

static std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
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

TEST(ParserSection29, UdpTableSpecialChars) {
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

// =============================================================================
// LRM section 29.3.6 -- UDP state table entries: symbol summary
// =============================================================================
// --- Combinational UDP table symbols ---
TEST(ParserSection29, TableSymbol0And1) {
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
  // Verify first row: inputs '0','0', output '0'
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], '0');
  EXPECT_EQ(udp->table[0].output, '0');
  // Verify last row: inputs '1','1', output '1'
  EXPECT_EQ(udp->table[3].inputs[0], '1');
  EXPECT_EQ(udp->table[3].inputs[1], '1');
  EXPECT_EQ(udp->table[3].output, '1');
}

TEST(ParserSection29, TableSymbolQuestionMark) {
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
  // Third row uses ? as input
  EXPECT_EQ(r.cu->udps[0]->table[2].inputs[0], '?');
  EXPECT_EQ(r.cu->udps[0]->table[2].output, 'x');
}

TEST(ParserSection29, TableSymbolX) {
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
  // Row with x input
  EXPECT_EQ(udp->table[4].inputs[0], 'x');
  EXPECT_EQ(udp->table[4].inputs[1], '?');
  EXPECT_EQ(udp->table[4].output, 'x');
}

TEST(ParserSection29, TableSymbolB) {
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

// --- Sequential UDP table symbols ---
TEST(ParserSection29, TableSymbolDashNoChange) {
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
  // Third row: no-change output
  EXPECT_EQ(udp->table[2].output, '-');
  // Current state field should be '?'
  EXPECT_EQ(udp->table[2].current_state, '?');
}

TEST(ParserSection29, TableEdgeSymbolsRAndF) {
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

}  // namespace
