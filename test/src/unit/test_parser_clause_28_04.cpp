// §28.4

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Minimum valid terminal counts ---
TEST(NInputGates, MinimumTwoTerminals) {
  auto r = Parse(
      "module m;\n"
      "  and (out, in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

TEST(NInputGateParsing, NamedAndGateParses) {
  auto r = Parse(
      "module m;\n"
      "  and g1(out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->gate_inst_name, "g1");
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(NInputGateParsing, UnnamedOrGateParses) {
  auto r = Parse(
      "module m;\n"
      "  or (out, a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kOr);
  EXPECT_TRUE(item->gate_inst_name.empty());
  ASSERT_EQ(item->gate_terminals.size(), 4);
}

TEST(NInputGateParsing, AllNInputGates) {
  auto r = Parse(
      "module m;\n"
      "  and (o, a, b);\n"
      "  nand (o, a, b);\n"
      "  or (o, a, b);\n"
      "  nor (o, a, b);\n"
      "  xor (o, a, b);\n"
      "  xnor (o, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 6);
  GateKind expected[] = {GateKind::kAnd, GateKind::kNand, GateKind::kOr,
                         GateKind::kNor, GateKind::kXor,  GateKind::kXnor};
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->items[i]->gate_kind, expected[i]);
  }
}

// --- Delay specification (delay2: zero, one, or two delays) ---
TEST(NInputGateParsing, SingleDelayAccepted) {
  auto r = Parse(
      "module m;\n"
      "  and #5 g(y, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(NInputGateParsing, TwoDelaysAccepted) {
  auto r = Parse(
      "module m;\n"
      "  and #(2, 3) g(y, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// delay3 is allowed only for tri-state/MOS gates; n-input gates cap at two.
TEST(NInputGateParsing, ThreeDelaysRejected) {
  auto r = Parse(
      "module m;\n"
      "  and #(1, 2, 3) g(y, a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// --- Terminal count lower bound (one output + at least one input) ---
TEST(NInputGateParsing, SingleTerminalRejected) {
  auto r = Parse(
      "module m;\n"
      "  and (y);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// --- First terminal must be a net lvalue (output position) ---
TEST(NInputGateParsing, OutputMustBeNetLvalue) {
  auto r = Parse(
      "module m;\n"
      "  and g(1, a, b);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
