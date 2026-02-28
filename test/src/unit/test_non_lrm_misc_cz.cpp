// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

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

static bool FindModuleInst(const std::vector<ModuleItem*>& items,
                           std::string_view module_name,
                           std::string_view expected_inst_name) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst &&
        item->inst_module == module_name) {
      EXPECT_EQ(item->inst_name, expected_inst_name);
      return true;
    }
  }
  return false;
}

struct UdpSpotCheck {
  size_t row;
  char input0;
  char output;
};

static void VerifyUdpTableSpotChecks(const UdpDecl* udp,
                                     const UdpSpotCheck checks[],
                                     size_t count) {
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(udp->table[checks[i].row].inputs[0], checks[i].input0);
    EXPECT_EQ(udp->table[checks[i].row].output, checks[i].output);
  }
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

static ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

static SpecifyItem* GetSoleSpecifyItem(ModuleItem* spec_block) {
  EXPECT_EQ(spec_block->specify_items.size(), 1u);
  if (spec_block->specify_items.empty()) return nullptr;
  return spec_block->specify_items[0];
}

struct SpecifyParseResult {
  ParseResult30 pr;
  ModuleItem* spec_block = nullptr;
  SpecifyItem* sole_item = nullptr;
};

static SpecifyParseResult ParseSpecifySingle(const std::string& src) {
  SpecifyParseResult result;
  result.pr = Parse(src);
  if (result.pr.cu == nullptr) return result;
  result.spec_block = FindSpecifyBlock(result.pr.cu->modules[0]->items);
  if (result.spec_block != nullptr) {
    result.sole_item = GetSoleSpecifyItem(result.spec_block);
  }
  return result;
}

static bool HasFullPathDecl(ModuleItem* spec_block) {
  for (auto* si : spec_block->specify_items) {
    if (si->kind == SpecifyItemKind::kPathDecl &&
        si->path.path_kind == SpecifyPathKind::kFull) {
      return true;
    }
  }
  return false;
}

static bool HasSpecifyItemKind(ModuleItem* spec_block, SpecifyItemKind kind) {
  for (auto* si : spec_block->specify_items) {
    if (si->kind == kind) return true;
  }
  return false;
}

namespace {

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

TEST(ParserSection29, TableEdgeSymbolStar) {
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

TEST(ParserSection29, TableEdgeSymbolsPAndN) {
  EXPECT_TRUE(
      ParseOk("primitive pos_neg(output reg q, input d, clk);\n"
              "  table\n"
              "    0 p : ? : 0;\n"
              "    1 p : ? : 1;\n"
              "    ? n : ? : -;\n"
              "  endtable\n"
              "endprimitive\n"));
}

TEST(ParserSection29, TableEdgeNotationParenthesized) {
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

// §3.7: "Designers can supplement the built-in primitives with user-defined
//        primitives (UDPs). A UDP is enclosed between the keywords
//        primitive...endprimitive."
//        Combinational UDP with truth table for gate-level modeling.
TEST(ParserClause03, Cl3_7_CombinationalUdp) {
  auto r = Parse(
      "primitive udp_or (output out, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "udp_or");
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 4u);
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[3].output, '1');
}

TEST(ParserSection29, UdpMultiple) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive buf2(output out, input in);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 2);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
  EXPECT_EQ(r.cu->udps[1]->name, "buf2");
}

TEST(ParserSection29, UdpCoexistsWithModule) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

// §3.7: Sequential UDP with initial statement — timing-accurate modeling
//        for sequential gate-level circuits.
TEST(ParserClause03, Cl3_7_SequentialUdp) {
  auto r = Parse(
      "primitive udp_latch (output reg q, input d, en);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    1 1 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "udp_latch");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
  ASSERT_EQ(udp->table.size(), 3u);
  // Sequential rows have current_state field
  EXPECT_EQ(udp->table[0].current_state, '?');
  EXPECT_EQ(udp->table[0].output, '1');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(ParserSection29, SequentialUdpInitial) {
  auto r = Parse(
      "primitive srff(output reg q, input s, r);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    1 0 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

TEST(ParserSection29, UdpInstance) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  wire a, b;\n"
      "  inv u1(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_TRUE(FindModuleInst(r.cu->modules[0]->items, "inv", "u1"));
}

TEST(ParserSection29, MixedLevelEdgeSensitive) {
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
  UdpSpotCheck checks[] = {
      {0, '?', '1'},  // Level-sensitive entry
      {2, 'r', '1'},  // Edge-sensitive entry
      {4, 'f', '-'},  // Falling edge with no-change output
  };
  VerifyUdpTableSpotChecks(udp, checks, std::size(checks));
}

TEST_F(SpecifyParseTest, SpecparamDeclaration) {
  auto* unit = Parse("module m; specparam tRISE = 10; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tRISE");
}

TEST_F(SpecifyParseTest, SpecparamWithRange) {
  auto* unit = Parse("module m; specparam [31:0] tDELAY = 100; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tDELAY");
}

TEST_F(SpecifyParseTest, MultipleSpecparams) {
  auto* unit =
      Parse("module m; specparam tRISE = 10; specparam tFALL = 12; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[0]->name, "tRISE");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecparam);
  EXPECT_EQ(items[1]->name, "tFALL");
}

TEST_F(SpecifyParseTest, EmptySpecifyBlock) {
  auto* unit = Parse("module m; specify endspecify endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecifyBlock);
}

TEST_F(SpecifyParseTest, SpecifyBlockWithTimingCheck) {
  auto* unit = Parse(
      "module m; specify $setup(data, posedge clk, 10); endspecify "
      "endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecifyBlock);
}

TEST_F(SpecifyParseTest, SpecifyBlockCoexistsWithOtherItems) {
  auto* unit =
      Parse("module m; logic a; specify endspecify assign a = 1; endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kContAssign);
}

// =============================================================================
// §30.2 Specparam declarations (inside specify)
// =============================================================================
TEST_F(SpecifyTest, SpecparamInsideSpecify) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tRISE = 10;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(item->param_name, "tRISE");
  EXPECT_NE(item->param_value, nullptr);
}

// =============================================================================
// Complex specify block with mixed items
// =============================================================================
TEST_F(SpecifyTest, MixedSpecifyBlockItems) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  specparam tPD = 5;\n"
      "  (a => b) = 5;\n"
      "  (a *> c) = (3, 4);\n"
      "  $setup(data, posedge clk, 10);\n"
      "  $hold(posedge clk, data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 5u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[3]->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(spec->specify_items[4]->kind, SpecifyItemKind::kTimingCheck);
}

// §3.3 Specify blocks
TEST(ParserClause03, Cl3_3_SpecifyBlock) {
  EXPECT_TRUE(
      ParseOk("module m (input a, output y);\n"
              "  assign y = a;\n"
              "  specify\n"
              "    (a => y) = 1.5;\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(ParserSection28, SpecifyBlockSimplePath) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_GE(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[0]->path.path_kind, SpecifyPathKind::kParallel);
}

TEST(ParserSection28, SpecifyBlockFullPath) {
  auto r = Parse(
      "module m(input a, b, output c);\n"
      "  specify\n"
      "    (a, b *> c) = (5, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(HasFullPathDecl(spec));
}

TEST(ParserSection28, SpecifyBlockWithSpecparam) {
  auto r = Parse(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    specparam tDelay = 10;\n"
      "    (clk => q) = tDelay;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(HasSpecifyItemKind(spec, SpecifyItemKind::kSpecparam));
  EXPECT_TRUE(HasSpecifyItemKind(spec, SpecifyItemKind::kPathDecl));
}

TEST(ParserSection28, Sec28_12_ConditionalPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, en, output b);\n"
      "  specify\n"
      "    if (en) (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_FALSE(si->path.is_ifnone);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "b");
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(ParserSection28, Sec28_12_IfnonePath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(ParserSection28, Sec28_12_PosedgeSensitivePath) {
  auto sp = ParseSpecifySingle(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "clk");
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0].name, "q");
}

TEST(ParserSection28, Sec28_12_NegedgeSensitivePath) {
  auto sp = ParseSpecifySingle(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    (negedge clk => q) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "clk");
}

TEST(ParserSection28, Sec28_12_MultipleSourceDestPorts) {
  auto sp = ParseSpecifySingle(
      "module m(input a, b, c, output x, y);\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 12;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  VerifyFullPathPorts(si, {"a", "b", "c"}, {"x", "y"});
}

TEST(ParserSection28, Sec28_12_PosedgeFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input clk, output q, qb);\n"
              "  specify\n"
              "    (posedge clk *> q, qb) = (3, 5);\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(ParserSection28, Sec28_12_ConditionalFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input a, b, en, output y);\n"
              "  specify\n"
              "    if (en) (a, b *> y) = 10;\n"
              "  endspecify\n"
              "endmodule\n"));
}

// =============================================================================
// §30.3 Path delay declarations
// =============================================================================
TEST_F(SpecifyTest, ParallelPathDelay) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = 5;\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_EQ(cu->modules.size(), 1u);
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(item->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(item->path.src_ports.size(), 1u);
  EXPECT_EQ(item->path.src_ports[0].name, "a");
  ASSERT_EQ(item->path.dst_ports.size(), 1u);
  EXPECT_EQ(item->path.dst_ports[0].name, "b");
  ASSERT_EQ(item->path.delays.size(), 1u);
}

TEST_F(SpecifyTest, FullPathDelay) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a *> b) = 10;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->path.path_kind, SpecifyPathKind::kFull);
}

}  // namespace
