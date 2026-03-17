#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(PrimitiveStrengthParsing, PullupStrength_Strength0Strength1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong0, pull1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);
  EXPECT_EQ(g->drive_strength1, 3u);
  EXPECT_EQ(g->gate_inst_name, "pu1");
}

TEST(PrimitiveStrengthParsing, PullupStrength_Weak0Supply1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak0, supply1) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);
  EXPECT_EQ(g->drive_strength1, 5u);
}

TEST(PrimitiveStrengthParsing, PullupStrength_Strength1Strength0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (supply1, weak0) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);
  EXPECT_EQ(g->drive_strength1, 5u);
}

TEST(PrimitiveStrengthParsing, PullupStrength_Highz1Strong0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (highz1, strong0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);
  EXPECT_EQ(g->drive_strength1, 1u);
}

TEST(PrimitiveStrengthParsing, PullupStrength_SingleStrength1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);
  EXPECT_EQ(g->drive_strength1, 4u);
}

TEST(PrimitiveStrengthParsing, PullupStrength_SingleSupply1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (supply1) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);
  EXPECT_EQ(g->drive_strength1, 5u);
}

TEST(PrimitiveStrengthParsing, PullupStrength_SingleWeak1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);
  EXPECT_EQ(g->drive_strength1, 2u);
}

TEST(PrimitiveStrengthParsing, PullupStrength_SinglePull1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (pull1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);
  EXPECT_EQ(g->drive_strength1, 3u);
}

TEST(PrimitiveStrengthParsing, PullupStrength_SingleHighz1) {
  auto r = Parse(
      "module m;\n"
      "  pullup (highz1) pu1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPullup);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 0u);
  EXPECT_EQ(g->drive_strength1, 1u);
}

TEST(PrimitiveStrengthParsing, PullupStrength_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak0, strong1) pu1(a), pu2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 2u);
  EXPECT_EQ(gates[0]->drive_strength1, 4u);
  EXPECT_EQ(gates[1]->drive_strength0, 2u);
  EXPECT_EQ(gates[1]->drive_strength1, 4u);
}

TEST(PrimitiveStrengthParsing, PullupStrength_SingleStrength1_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pullup (pull1) pu1(a), pu2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 0u);
  EXPECT_EQ(gates[0]->drive_strength1, 3u);
  EXPECT_EQ(gates[1]->drive_strength0, 0u);
  EXPECT_EQ(gates[1]->drive_strength1, 3u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_Strength0Strength1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0, pull1) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);
  EXPECT_EQ(g->drive_strength1, 3u);
  EXPECT_EQ(g->gate_inst_name, "pd1");
}

TEST(PrimitiveStrengthParsing, PulldownStrength_Supply0Weak1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (supply0, weak1) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);
  EXPECT_EQ(g->drive_strength1, 2u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_Pull0Highz1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0, highz1) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 3u);
  EXPECT_EQ(g->drive_strength1, 1u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_Strength1Strength0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull1, strong0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);
  EXPECT_EQ(g->drive_strength1, 3u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_Highz1Supply0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (highz1, supply0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);
  EXPECT_EQ(g->drive_strength1, 1u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_SingleStrength0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);
  EXPECT_EQ(g->drive_strength1, 0u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_SingleSupply0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (supply0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);
  EXPECT_EQ(g->drive_strength1, 0u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_SingleWeak0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (weak0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);
  EXPECT_EQ(g->drive_strength1, 0u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_SinglePull0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 3u);
  EXPECT_EQ(g->drive_strength1, 0u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_SingleHighz0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (highz0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 1u);
  EXPECT_EQ(g->drive_strength1, 0u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0, weak1) pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 4u);
  EXPECT_EQ(gates[0]->drive_strength1, 2u);
  EXPECT_EQ(gates[1]->drive_strength0, 4u);
  EXPECT_EQ(gates[1]->drive_strength1, 2u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_SingleStrength0_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0) pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 3u);
  EXPECT_EQ(gates[0]->drive_strength1, 0u);
  EXPECT_EQ(gates[1]->drive_strength0, 3u);
  EXPECT_EQ(gates[1]->drive_strength1, 0u);
}

TEST(PrimitiveStrengthParsing, PulldownStrength_AllStrength0Values) {
  EXPECT_TRUE(ParseOk("module m; pulldown (highz0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (weak0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (pull0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (strong0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (supply0) (out); endmodule"));
}

TEST(PrimitiveStrengthParsing, PullupStrength_AllStrength1Values) {
  EXPECT_TRUE(ParseOk("module m; pullup (highz1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (weak1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (pull1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (strong1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (supply1) (out); endmodule"));
}

TEST(PrimitiveStrengthParsing, Error_PulldownSingleStrength1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong1) pd1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveStrengthParsing, Error_PulldownSingleWeak1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (weak1) pd1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveStrengthParsing, Error_PulldownSinglePull1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull1) pd1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveStrengthParsing, Error_PulldownSingleSupply1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (supply1) pd1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveStrengthParsing, Error_PulldownSingleHighz1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (highz1) pd1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveStrengthParsing, Error_PullupSingleStrength0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (strong0) pu1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveStrengthParsing, Error_PullupSingleWeak0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (weak0) pu1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveStrengthParsing, Error_PullupSinglePull0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (pull0) pu1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveStrengthParsing, Error_PullupSingleHighz0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (highz0) pu1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(PrimitiveStrengthParsing, Error_PullupSingleSupply0) {
  auto r = Parse(
      "module m;\n"
      "  pullup (supply0) pu1(out);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
