#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

// Every instance in a comma-separated gate-instance list must inherit the
// single drive-strength spec written before the list.
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

// Same requirement, delay side: one shared delay spec applies to every
// instance in the comma-separated list.
TEST(PrimitiveInstantiationParsing, GateInst_SharedDelayAcrossInstances) {
  auto r = Parse(
      "module m;\n"
      "  or #5 o1(out1, a, b), o2(out2, c, d);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_NE(gates[0]->gate_delay, nullptr);
  EXPECT_NE(gates[1]->gate_delay, nullptr);
}

// Two-value (rise, fall) delay must propagate identically to every instance.
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
