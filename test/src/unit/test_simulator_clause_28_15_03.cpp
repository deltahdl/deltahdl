#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §28.15.3 defines one runtime rule with two duals. A supply0 net models a
// ground connection: it carries value 0 at supply driving strength. A supply1
// net models a power-supply connection: it carries value 1 at supply driving
// strength. The net type is produced by a `supply0`/`supply1` declaration, so
// every test builds the net from real source and drives it through
// parse -> elaborate -> lower -> simulate, observing the value and strength the
// production resolver (net.cpp ResolveSupplyNet) installs. Because a supply net
// is a constant connection, its canonical form has no explicit source; the
// production Net::Resolve gate resolves a driverless supply net just as it does
// tri0/tri1. The final pair drives an opposing strong continuous assignment to
// confirm supply strength dominates strong, the adversarial form of the rule.

// ---- Scalar declared net, no source (canonical constant connection) ----

// A driverless scalar supply0 net settles to 0 at supply strength.
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

// The dual: a driverless scalar supply1 net settles to 1 at supply strength.
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

// ---- Vector declared net, no source (multi-bit input form) ----

// A packed-vector supply0 declaration carries 0 at supply strength on every
// bit.
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

// The dual: a packed-vector supply1 declaration carries 1 at supply strength on
// every bit.
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

// ---- Wide (multi-word) declared net, no source ----

// The rule holds bit-for-bit across a vector wider than one machine word,
// exercising the per-word fill in the resolver.
TEST(SupplyNetStrengths, DeclaredSupply1WideVectorUndrivenAllBitsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  supply1 [95:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  const auto& v = w->resolved->value;
  ASSERT_GT(v.nwords, 1u);
  for (uint32_t i = 0; i < v.nwords; ++i) {
    uint32_t bits = 96 - i * 64;
    uint64_t mask = bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1;
    EXPECT_EQ(v.words[i].aval & mask, mask);
    EXPECT_EQ(v.words[i].bval & mask, 0u);
  }
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s1_lo, Strength::kSupply);
}

TEST(SupplyNetStrengths, DeclaredSupply0WideVectorUndrivenAllBitsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  supply0 [95:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  const auto& v = w->resolved->value;
  ASSERT_GT(v.nwords, 1u);
  for (uint32_t i = 0; i < v.nwords; ++i) {
    uint32_t bits = 96 - i * 64;
    uint64_t mask = bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1;
    EXPECT_EQ(v.words[i].aval & mask, 0u);
    EXPECT_EQ(v.words[i].bval & mask, 0u);
  }
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kSupply);
  EXPECT_EQ(w->resolved_strength.s0_lo, Strength::kSupply);
}

// ---- Contended by an opposing strong source (adversarial / negative form)
// ----

// Supply is the strongest drive: a continuous assignment pushing the opposite
// value at strong strength does not override a supply0 net, which stays 0 at
// supply strength. This is the negative form -- an ordinary net would take the
// driver's value, but supply strength dominates strong.
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

// The dual: a strong 0 source does not override a supply1 net, which stays 1 at
// supply strength.
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

}  // namespace
