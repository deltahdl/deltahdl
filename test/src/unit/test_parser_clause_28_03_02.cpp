// §28.3.2: The drive strength specification

#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

// =============================================================
// §28.3: Gate and switch declaration syntax
// =============================================================
// §28.3: "Multiple instances of the one type ... shall have the same
//  drive strength and delay specification."
// --- §28.3.1: Gate type specification ---
// §28.3.1: Declaration shall begin with keyword naming the gate type.
// Table 28-1: all 26 built-in gate/switch types.
// --- §28.3.2: Drive strength specification ---
// §28.3.2: Only certain gate types can have drive strength.
TEST(GateDecl, StrengthSpecValidForNInputGates) {
  constexpr GateType kNInputGates[] = {
      GateType::kAnd, GateType::kNand, GateType::kOr,
      GateType::kNor, GateType::kXor,  GateType::kXnor,
  };
  for (auto gate : kNInputGates) {
    EXPECT_TRUE(CanHaveStrengthSpec(gate));
  }
}

TEST(GateDecl, StrengthSpecValidForEnableGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBufif0));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBufif1));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNotif0));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNotif1));
}

TEST(GateDecl, StrengthSpecValidForNOutputGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kBuf));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kNot));
}

TEST(ParserAnnexA, A3GateInstWithStrengthAndDelay) {
  auto r = Parse("module m; and (strong0, weak1) #5 g(y, a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA301, GateInst_EnableWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  bufif0 (strong0, pull1) b1(out, in, ctrl);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(ParserA301, GateInst_NInputWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  and (pull0, pull1) a1(out, a, b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
}

TEST(ParserA301, GateInst_NOutputWithStrength) {
  auto r = Parse(
      "module m;\n"
      "  buf (strong0, strong1) b1(out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_NE(g->drive_strength0, 0);
  EXPECT_NE(g->drive_strength1, 0);
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

TEST(ParserA302, PulldownStrength_SingleWeak0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (weak0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 2u);  // weak0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SinglePull0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 3u);  // pull0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

TEST(ParserA302, PulldownStrength_SingleHighz0) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (highz0) pd1(out);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kPulldown);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->drive_strength0, 1u);  // highz0
  EXPECT_EQ(g->drive_strength1, 0u);  // none
}

// -----------------------------------------------------------------------------
// Combination: strength with multiple instances
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (strong0, weak1) pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 4u);  // strong0
  EXPECT_EQ(gates[0]->drive_strength1, 2u);  // weak1
  EXPECT_EQ(gates[1]->drive_strength0, 4u);  // strong0
  EXPECT_EQ(gates[1]->drive_strength1, 2u);  // weak1
}

TEST(ParserA302, PulldownStrength_SingleStrength0_MultipleInstances) {
  auto r = Parse(
      "module m;\n"
      "  pulldown (pull0) pd1(a), pd2(b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto gates = FindAllGates(r.cu->modules[0]->items);
  ASSERT_EQ(gates.size(), 2u);
  EXPECT_EQ(gates[0]->drive_strength0, 3u);  // pull0
  EXPECT_EQ(gates[0]->drive_strength1, 0u);  // none
  EXPECT_EQ(gates[1]->drive_strength0, 3u);  // pull0
  EXPECT_EQ(gates[1]->drive_strength1, 0u);  // none
}

// -----------------------------------------------------------------------------
// All strength0 values exercised in pulldown_strength
// -----------------------------------------------------------------------------
TEST(ParserA302, PulldownStrength_AllStrength0Values) {
  // highz0=1, weak0=2, pull0=3, strong0=4, supply0=5
  EXPECT_TRUE(ParseOk("module m; pulldown (highz0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (weak0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (pull0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (strong0) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pulldown (supply0) (out); endmodule"));
}

// -----------------------------------------------------------------------------
// All strength1 values exercised in pullup_strength
// -----------------------------------------------------------------------------
TEST(ParserA302, PullupStrength_AllStrength1Values) {
  // highz1=1, weak1=2, pull1=3, strong1=4, supply1=5
  EXPECT_TRUE(ParseOk("module m; pullup (highz1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (weak1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (pull1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (strong1) (out); endmodule"));
  EXPECT_TRUE(ParseOk("module m; pullup (supply1) (out); endmodule"));
}

}  // namespace
