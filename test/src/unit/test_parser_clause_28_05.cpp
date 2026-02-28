// §28.5: buf and not gates

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.3.1 Production #1: gate_instantiation (n_output_gatetype alternative)
// gate_instantiation ::=
//   n_output_gatetype [drive_strength] [delay2] n_output_gate_instance
//                     {, n_output_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_BufBasic) {
  auto r = Parse(
      "module m;\n"
      "  buf (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, GateInst_NotBasic) {
  auto r = Parse(
      "module m;\n"
      "  not (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, GateInst_NOutputMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  buf (o1, o2, o3, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

// =============================================================================
// A.3.1 Production #6: n_output_gate_instance
// n_output_gate_instance ::= [name_of_instance]
//   ( output_terminal {, output_terminal} , input_terminal )
// =============================================================================
TEST(ParserA301, NOutputGateInst_SingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  buf b1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA301, NOutputGateInst_ThreeOutputs) {
  auto r = Parse(
      "module m;\n"
      "  not n1(o1, o2, o3, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

TEST(ParserA301, NOutputGateInst_Unnamed) {
  auto r = Parse(
      "module m;\n"
      "  buf (o1, o2, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_TRUE(g->gate_inst_name.empty());
  EXPECT_EQ(g->gate_terminals.size(), 3u);
}

// =============================================================================
// A.3.4 Production #5: n_output_gatetype ::= buf | not
// =============================================================================
TEST(ParserA304, NOutputGatetype_Buf) {
  auto r = Parse(
      "module m;\n"
      "  buf (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(ParserA304, NOutputGatetype_Not) {
  auto r = Parse(
      "module m;\n"
      "  not (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNot);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

}  // namespace
