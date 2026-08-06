#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(PrimitiveInstantiationParsing, GateInst_SharedStrengthAcrossInstances) {
  auto r = Parse(
      "module m;\n"
      "  and (weak0, weak1) a1(o1, i1, i2), a2(o2, i3, i4);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, gates[1]->drive_strength0);
  EXPECT_EQ(gates[0]->drive_strength1, gates[1]->drive_strength1);
}

// §28.3 states that when several primitives are written as one comma-separated
// declaration, every instance shares the same drive strength AND delay
// specification. The shared-strength and shared-delay facets are exercised in
// isolation elsewhere; this checks the conjunction holds across a list of more
// than two instances — each of the three gates must carry the identical
// strength pair and the identical rise/fall delay parsed once for the list.
TEST(PrimitiveInstantiationParsing, GateInst_SharedStrengthAndDelayAcrossList) {
  auto r = Parse(
      "module m;\n"
      "  nand (strong0, weak1) #(2, 3) g1(o1, a, b), g2(o2, c, d), g3(o3, e, "
      "f);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 3u);
  EXPECT_EQ(gates[0]->drive_strength0, 4u);  // strong0
  EXPECT_EQ(gates[0]->drive_strength1, 2u);  // weak1
  for (auto* g : gates) {
    EXPECT_EQ(g->drive_strength0, gates[0]->drive_strength0);
    EXPECT_EQ(g->drive_strength1, gates[0]->drive_strength1);
    ASSERT_NE(g->gate_delay, nullptr);
    EXPECT_EQ(g->gate_delay->int_val, 2u);
    ASSERT_NE(g->gate_delay_fall, nullptr);
    EXPECT_EQ(g->gate_delay_fall->int_val, 3u);
  }
}

// §28.3 enumerates the components a gate/switch declaration may carry: the
// primitive keyword, an optional drive strength, an optional propagation
// delay, an optional instance identifier, an optional range for an array of
// instances, and the terminal connection list. This exercises one declaration
// that supplies every optional component at once and checks each lands on the
// parsed instance. The array-range semantics themselves belong to §28.3.5; here
// we only observe that the range component is accepted and recorded.
TEST(PrimitiveInstantiationParsing, GateInst_AllDeclarationComponents) {
  auto r = Parse(
      "module m;\n"
      "  and (strong0, strong1) #3 g[3:0](o, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 1u);
  auto* g = gates[0];
  EXPECT_EQ(g->gate_kind, GateKind::kAnd);  // keyword
  EXPECT_EQ(g->drive_strength0, 4u);        // drive strength
  EXPECT_EQ(g->drive_strength1, 4u);
  EXPECT_NE(g->gate_delay, nullptr);       // propagation delay
  EXPECT_EQ(g->gate_inst_name, "g");       // instance identifier
  EXPECT_NE(g->inst_range_left, nullptr);  // range for array
  EXPECT_NE(g->inst_range_right, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);  // terminal connection list
}

// §28.3 head states its declaration structure applies to a gate OR a switch
// instance. The AllDeclarationComponents test above uses a gate; this exercises
// the switch input form: an nmos switch declaration carrying an optional delay,
// an instance identifier, an array range, and the terminal connection list.
// (A switch cannot take a drive strength — that is §28.3.2's restriction — so
// the strength component is absent here.)
TEST(PrimitiveInstantiationParsing, SwitchInstanceDeclarationComponents) {
  auto r = Parse(
      "module m;\n"
      "  wire o, i, c;\n"
      "  nmos #3 s[1:0](o, i, c);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 1u);
  auto* g = gates[0];
  EXPECT_EQ(g->gate_kind, GateKind::kNmos);  // switch keyword
  EXPECT_NE(g->gate_delay, nullptr);         // propagation delay
  EXPECT_EQ(g->gate_inst_name, "s");         // instance identifier
  EXPECT_NE(g->inst_range_left, nullptr);    // array range
  EXPECT_NE(g->inst_range_right, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 3u);  // terminal connection list
}

// §28.3 head: a comma-separated list of switch instances shares one delay
// specification, exactly as for gates.
TEST(PrimitiveInstantiationParsing, SwitchListSharesOneDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire o1, o2, i1, i2, c1, c2;\n"
      "  nmos #4 s1(o1, i1, c1), s2(o2, i2, c2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  for (auto* g : gates) {
    ASSERT_NE(g->gate_delay, nullptr);
    EXPECT_EQ(g->gate_delay->int_val, 4u);
  }
}

TEST(GateDelayParsing, MultipleInstancesWithRiseFallDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y1, y2, a, b;\n"
      "  and #(4, 6) g1(y1, a, b), g2(y2, a, b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

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

}  // namespace
