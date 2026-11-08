#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
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

}  // namespace
