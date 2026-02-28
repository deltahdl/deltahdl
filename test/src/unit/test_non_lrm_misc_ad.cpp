// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA301, GateInst_AllPassSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tran  t1(a, b);\n"
              "  rtran rt1(a, b);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_AllPassEnSwitchTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  tranif0  t0(a, b, c);\n"
              "  tranif1  t1(a, b, c);\n"
              "  rtranif0 rt0(a, b, c);\n"
              "  rtranif1 rt1(a, b, c);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_StrengthOrder_Strength1First) {
  auto r = Parse(
      "module m;\n"
      "  and (pull1, strong0) a1(out, in1, in2);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(ParserA301, GateInst_DelayWithMinTypMax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and #(1:2:3, 4:5:6) a1(out, in1, in2);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_ComplexTerminalExpressions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  and a1(out[0], in1[3:0], in2[7:4]);\n"
              "endmodule\n"));
}

TEST(ParserA301, GateInst_NamedUnnamedMixedInMulti) {
  auto r = Parse(
      "module m;\n"
      "  and a1(o1, i1, i2), a2(o2, i3, i4), a3(o3, i5, i6);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  EXPECT_EQ(gates.size(), 3u);
  EXPECT_EQ(gates[0]->gate_inst_name, "a1");
  EXPECT_EQ(gates[1]->gate_inst_name, "a2");
  EXPECT_EQ(gates[2]->gate_inst_name, "a3");
}

TEST(ParserA301, GateInst_SharedStrengthAcrossInstances) {
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

TEST(ParserA301, GateInst_SharedDelayAcrossInstances) {
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

// =============================================================================
// A.3.2 Primitive strengths
//
// pulldown_strength ::=
//   ( strength0 , strength1 )
//   | ( strength1 , strength0 )
//   | ( strength0 )
//
// pullup_strength ::=
//   ( strength0 , strength1 )
//   | ( strength1 , strength0 )
//   | ( strength1 )
// =============================================================================
// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength0 , strength1 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_Strength0Strength1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0, pull1) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 3u);  // pull1
  EXPECT_EQ(g->gate_inst_name, "pd1");
}

TEST(ParserA302, PulldownStrength_Supply0Weak1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (supply0, weak1) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);  // supply0
  EXPECT_EQ(g->drive_strength1, 2u);  // weak1
}

TEST(ParserA302, PulldownStrength_Pull0Highz1) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0, highz1) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 3u);  // pull0
  EXPECT_EQ(g->drive_strength1, 1u);  // highz1
}

// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength1 , strength0 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_Strength1Strength0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull1, strong0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 3u);  // pull1
}

TEST(ParserA302, PulldownStrength_Highz1Supply0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (highz1, supply0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);  // supply0
  EXPECT_EQ(g->drive_strength1, 1u);  // highz1
}

// -----------------------------------------------------------------------------
// Production #1: pulldown_strength
// pulldown_strength ::= ( strength0 )
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_SingleStrength0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 4u);  // strong0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SingleSupply0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (supply0) (out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 5u);  // supply0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

}  // namespace
