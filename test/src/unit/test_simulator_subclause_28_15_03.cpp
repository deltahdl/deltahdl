#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_net_declaration_places.h"
#include "helpers_wide_undriven_net.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SupplyNetStrengths, DeclaredSupply0UndrivenResolvesZeroWithSupply) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  supply0 w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 0u);
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s0_lo, Strength::kSupply);
}

TEST(SupplyNetStrengths, DeclaredSupply1UndrivenResolvesOneWithSupply) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  supply1 w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s1_lo, Strength::kSupply);
}

TEST(SupplyNetStrengths, DeclaredSupply0VectorUndrivenAllBitsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  supply0 [7:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0xFF, 0x00u);
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s0_lo, Strength::kSupply);
}

TEST(SupplyNetStrengths, DeclaredSupply1VectorUndrivenAllBitsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  supply1 [7:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0xFF, 0xFFu);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s1_lo, Strength::kSupply);
}

TEST(SupplyNetStrengths, DeclaredSupply1WideVectorUndrivenAllBitsOne) {
  SimFixture f;
  auto* w = ExpectWideUndrivenNetBits(f, "supply1", true);
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s1_lo, Strength::kSupply);
}

TEST(SupplyNetStrengths, DeclaredSupply0WideVectorUndrivenAllBitsZero) {
  SimFixture f;
  auto* w = ExpectWideUndrivenNetBits(f, "supply0", false);
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s0_lo, Strength::kSupply);
}

TEST(SupplyNetStrengths, Supply0NotOverriddenByStrongOppositeSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  supply0 w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 0u);
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s0_lo, Strength::kSupply);
}

TEST(SupplyNetStrengths, Supply1NotOverriddenByStrongOppositeSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  supply1 w;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s1_lo, Strength::kSupply);
}

void ExpectSupplyX(const std::string& body) {
  SimFixture f;
  auto* design = ElaborateSrc("module m;\n" + body + "endmodule\n", f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.words[0].aval & 0x1, 1u);
  EXPECT_EQ(w->resolved->value.words[0].bval & 0x1, 1u);
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kSupply);
}

TEST(SupplyNetStrengths, Supply0ContendedAtSupplyStrengthResolvesToX) {
  ExpectSupplyX(
      "  supply0 w;\n"
      "  buf (supply0, supply1) g (w, 1'b1);\n");
}

TEST(SupplyNetStrengths, Supply1ContendedAtSupplyStrengthResolvesToX) {
  ExpectSupplyX(
      "  supply1 w;\n"
      "  buf (supply0, supply1) g (w, 1'b0);\n");
}

TEST(SupplyNetStrengths, AnExplicitDataTypeKeepsTheSupplyStrength) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  supply0 logic a;\n"
      "  supply1 logic [1:0] b;\n"
      "  supply0 logic [3:0] c;\n"
      "  initial #1 $display(\"%v %v %v %v\", a, b[1], b[0], c[2]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Su0 Su1 Su1 Su0\n");
}

TEST(SupplyNetStrengths, ASupplyNetIsSupplyInEveryPlaceItIsDeclared) {
  for (auto place :
       {NetDeclarationPlace::kCompilationUnit, NetDeclarationPlace::kInterface,
        NetDeclarationPlace::kGenerate, NetDeclarationPlace::kProgram}) {
    EXPECT_EQ(NetStrengthDeclaredIn(place, "supply0 n;"), "Su0\n")
        << static_cast<int>(place);
    EXPECT_EQ(NetStrengthDeclaredIn(place, "supply1 n;"), "Su1\n")
        << static_cast<int>(place);
  }
}

}  // namespace
