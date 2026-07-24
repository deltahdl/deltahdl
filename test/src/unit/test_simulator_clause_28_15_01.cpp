#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §28.15.1 defines two runtime rules. A tri0 net models a resistive pulldown:
// with no overriding source it settles to value 0 at pull strength. A tri1 net
// models a resistive pullup: with no overriding source it settles to value 1 at
// pull strength. The net type is produced by a `tri0`/`tri1` declaration, so
// every test here builds the net from real source and drives it through
// parse -> elaborate -> lower -> simulate, observing the pull default the
// production lowerer installs (sim_context.cpp resolves a driverless tri0/tri1
// at creation; net.cpp FixupTriPull re-applies the default to any
// high-impedance bit after a driver update). The dependency §28.12.1 supplies
// the multi-source combining exercised by the last pair of tests.

// ---- Scalar declared net, no source ----

// A driverless scalar tri0 net pulls down to 0 at pull strength.
TEST(Tri0Tri1NetStrengths, DeclaredTri0UndrivenResolvesZeroWithPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri0 w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 0u);
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(w->resolved_strength.s0_lo, Strength::kPull);
}

// A driverless scalar tri1 net pulls up to 1 at pull strength.
TEST(Tri0Tri1NetStrengths, DeclaredTri1UndrivenResolvesOneWithPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri1 w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kPull);
  EXPECT_EQ(w->resolved_strength.s1_lo, Strength::kPull);
}

// ---- Vector declared net, no source (multi-bit input form) ----

// A packed-vector tri0 declaration pulls every bit down to 0.
TEST(Tri0Tri1NetStrengths, DeclaredTri0VectorUndrivenAllBitsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri0 [7:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0xFF, 0x00u);
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kPull);
}

// A packed-vector tri1 declaration pulls every bit up to 1.
TEST(Tri0Tri1NetStrengths, DeclaredTri1VectorUndrivenAllBitsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri1 [7:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0xFF, 0xFFu);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kPull);
}

// ---- Wide (multi-word) declared net, no source ----

// The rule holds bit-for-bit across a vector wider than one machine word.
TEST(Tri0Tri1NetStrengths, DeclaredTri0WideVectorUndrivenAllBitsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri0 [95:0] w;\n"
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
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kPull);
}

TEST(Tri0Tri1NetStrengths, DeclaredTri1WideVectorUndrivenAllBitsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri1 [95:0] w;\n"
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
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kPull);
}

// ---- Overriding source (opposite value) ----

// A real driver of the opposite value overrides the pulldown: the source, not
// the tri0 default, decides the settled value.
TEST(Tri0Tri1NetStrengths, DeclaredTri0OverriddenBySourceValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri0 w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 1u);
}

// The dual: a driver of 0 overrides the tri1 pullup default.
TEST(Tri0Tri1NetStrengths, DeclaredTri1OverriddenBySourceValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri1 w;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 0u);
}

// ---- High-Z source is not an overriding source (negative form) ----

// A high-impedance source does not override: a tri0 net still pulls down to
// 0/pull when its only driver contributes z.
TEST(Tri0Tri1NetStrengths, DeclaredTri0HighZSourceDoesNotOverride) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri0 w;\n"
      "  assign w = 1'bz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 0u);
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kPull);
}

// The dual: a z source leaves a tri1 net pulled up to 1/pull.
TEST(Tri0Tri1NetStrengths, DeclaredTri1HighZSourceDoesNotOverride) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri1 w;\n"
      "  assign w = 1'bz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kPull);
}

// ---- Per-bit qualifier: a source overrides only the bits it drives ----

// "In the absence of an overriding source" applies bit by bit: a part-select
// driver decides its own bits while every undriven bit is pulled to the
// net-type default. A driven low nibble on a tri0 vector leaves the high nibble
// pulled to 0.
TEST(Tri0Tri1NetStrengths,
     DeclaredTri0PartSelectDriverOverridesOnlyDrivenBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri0 [7:0] w;\n"
      "  assign w[3:0] = 4'hF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0xFF, 0x0Fu);
}

// The dual: a driven low nibble of 0 on a tri1 vector leaves the high nibble
// pulled up to 1.
TEST(Tri0Tri1NetStrengths,
     DeclaredTri1PartSelectDriverOverridesOnlyDrivenBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri1 [7:0] w;\n"
      "  assign w[3:0] = 4'h0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0xFF, 0xF0u);
}

// ---- Multiple combining sources (consumes §28.12.1) ----

// With two continuous sources, one high-impedance and one driving a real value,
// §28.12.1 combines them and the driven value overrides both the z source and
// the tri0 pull default.
TEST(Tri0Tri1NetStrengths, DeclaredTri0MultiSourceDrivenOverridesHighZAndPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri0 w;\n"
      "  assign w = 1'bz;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 1u);
}

// When every combining source is high-impedance, none is overriding, so the
// tri1 net keeps its pullup default of 1/pull.
TEST(Tri0Tri1NetStrengths, DeclaredTri1MultiSourceAllHighZKeepsPull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  tri1 w;\n"
      "  assign w = 1'bz;\n"
      "  assign w = 1'bz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* w = f.ctx.FindNet("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kPull);
}

}  // namespace
