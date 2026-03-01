// §28.4: and, nand, nor, or, xor, and xnor gates

#include "fixture_parser.h"

using namespace delta;

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

namespace {

// ---------------------------------------------------------------------------
// Delay propagation across multiple instances
// ---------------------------------------------------------------------------
// Gate delay shared across comma-separated instances.
TEST(ParserA223, Delay3GateMultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  wire y1, y2, a, b;\n"
      "  and #(4, 6) g1(y1, a, b), g2(y2, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // wire y1, y2, a, b creates 4 items; gates are items[4] and items[5]
  auto* g1 = r.cu->modules[0]->items[4];
  auto* g2 = r.cu->modules[0]->items[5];
  ASSERT_NE(g1->gate_delay, nullptr);
  EXPECT_EQ(g1->gate_delay->int_val, 4u);
  ASSERT_NE(g1->gate_delay_fall, nullptr);
  EXPECT_EQ(g1->gate_delay_fall->int_val, 6u);
  ASSERT_NE(g2->gate_delay, nullptr);
  EXPECT_EQ(g2->gate_delay->int_val, 4u);
  ASSERT_NE(g2->gate_delay_fall, nullptr);
  EXPECT_EQ(g2->gate_delay_fall->int_val, 6u);
}

// =============================================================================
// A.3 -- Primitive instances (gate_instantiation)
// =============================================================================
TEST(ParserAnnexA, A3GateInstNInput) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b, c);\n"
      "  nand g2(y2, a, b);\n"
      "  xor g3(y3, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int gate_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGateInst) gate_count++;
  }
  EXPECT_EQ(gate_count, 3);
}

// =============================================================================
// A.3.1 Production #1: gate_instantiation (n_input_gatetype alternative)
// gate_instantiation ::=
//   n_input_gatetype [drive_strength] [delay2] n_input_gate_instance
//                    {, n_input_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_AndBasic) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, GateInst_NandBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nand (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_OrBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  or (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_NorBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nor (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_XorBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  xor (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_XnorBasic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  xnor (out, a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_NInputWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  or #(3, 5) o1(out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->gate_delay, nullptr);
  EXPECT_NE(g->gate_delay_fall, nullptr);
}

TEST(ParserA301, GateInst_NInputMultipleInputs) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 5u);
}

// =============================================================================
// A.3.1 Production #5: n_input_gate_instance
// n_input_gate_instance ::= [name_of_instance]
//   ( output_terminal , input_terminal {, input_terminal} )
// =============================================================================
TEST(ParserA301, NInputGateInst_TwoInputs) {
  auto r = Parse(
      "module m;\n"
      "  and a1(out, in1, in2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_inst_name, "a1");
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA301, NInputGateInst_FourInputs) {
  auto r = Parse(
      "module m;\n"
      "  nand n1(out, a, b, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 5u);
}

TEST(ParserA301, NInputGateInst_EightInputs) {
  auto r = Parse(
      "module m;\n"
      "  xor x1(out, a, b, c, d, e, f, g, h);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 9u);
}

TEST(ParserA301, NInputGateInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  or (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
}

// =============================================================================
// Additional gate_instantiation combinations
// =============================================================================
TEST(ParserA301, GateInst_AllNInputGateTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and  a1(o, i1, i2);\n"
              "  nand n1(o, i1, i2);\n"
              "  or   o1(o, i1, i2);\n"
              "  nor  r1(o, i1, i2);\n"
              "  xor  x1(o, i1, i2);\n"
              "  xnor z1(o, i1, i2);\n"
              "endmodule\n"));
}

// =============================================================================
// A.3.4 Production #4: n_input_gatetype ::= and | nand | or | nor | xor | xnor
// =============================================================================
TEST(ParserA304, NInputGatetype_And) {
  auto r = Parse(
      "module m;\n"
      "  and (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Nand) {
  auto r = Parse(
      "module m;\n"
      "  nand (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Or) {
  auto r = Parse(
      "module m;\n"
      "  or (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kOr);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Nor) {
  auto r = Parse(
      "module m;\n"
      "  nor (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Xor) {
  auto r = Parse(
      "module m;\n"
      "  xor (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

TEST(ParserA304, NInputGatetype_Xnor) {
  auto r = Parse(
      "module m;\n"
      "  xnor (out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kXnor);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);
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

// delay2: two values on n_input gate (rise, fall).
TEST(ParserA223, Delay2NInputGateTwoValues) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, b;\n"
      "  or #(3, 5) g1(y, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[3];
  ASSERT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_delay->int_val, 3u);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  EXPECT_EQ(item->gate_delay_fall->int_val, 5u);
}

}  // namespace
