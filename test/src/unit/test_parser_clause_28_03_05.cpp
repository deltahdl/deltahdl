// §28.3.5 — The range specification on gate/switch primitive instances.
// Each test here exercises parsing of the optional [lhi:rhi] array-of-instances
// syntax that follows the instance identifier.

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(GateLevelModelingParsing, GateArrayRange) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nand n[0:3](out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kNand);
}

TEST(GateLevelModelingParsing, GateArrayWithDelay) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  and #5 g[0:7](out, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_NE(item->gate_delay, nullptr);
}

TEST(GateLevelModelingParsing, GateArrayRangeBoundsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  nand n[0:3](out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->inst_range_left, nullptr);
  EXPECT_NE(g->inst_range_right, nullptr);
}

TEST(GateLevelModelingParsing, GateNoRangeHasNullBounds) {
  auto r = Parse(
      "module m;\n"
      "  nand n1(out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->inst_range_left, nullptr);
  EXPECT_EQ(g->inst_range_right, nullptr);
}

TEST(GateLevelModelingParsing, GateArrayReversedBounds) {
  auto r = Parse(
      "module m;\n"
      "  nand n[3:0](out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNand);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->inst_range_left, nullptr);
  EXPECT_NE(g->inst_range_right, nullptr);
}

TEST(GateLevelModelingParsing, GateArrayEqualBounds) {
  auto r = Parse(
      "module m;\n"
      "  and g[5:5](out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->inst_range_left, nullptr);
  EXPECT_NE(g->inst_range_right, nullptr);
}

TEST(GateLevelModelingParsing, SwitchArrayOnNmos) {
  auto r = Parse(
      "module m;\n"
      "  nmos n[0:3](out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->inst_range_left, nullptr);
  EXPECT_NE(g->inst_range_right, nullptr);
}

TEST(GateLevelModelingParsing, GateArrayMixedArrayAndSingleInList) {
  auto r = Parse(
      "module m;\n"
      "  and a1(o1, x1, y1), b[0:3](o2, x2, y2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->inst_range_left, nullptr);
  EXPECT_EQ(gates[0]->inst_range_right, nullptr);
  EXPECT_NE(gates[1]->inst_range_left, nullptr);
  EXPECT_NE(gates[1]->inst_range_right, nullptr);
}

TEST(GateLevelModelingParsing, GateArrayDuplicateIdentifierIsError) {
  auto r = Parse(
      "module m;\n"
      "  nand #2 t_nand[0:3](o1, a, b), t_nand[4:7](o2, c, d);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
