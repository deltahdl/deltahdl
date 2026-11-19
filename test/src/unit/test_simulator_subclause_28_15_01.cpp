#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_net_declaration_places.h"
#include "helpers_wide_undriven_net.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(Tri0Tri1NetStrengths, DeclaredTri0WideVectorUndrivenAllBitsZero) {
  SimFixture f;
  auto* w = ExpectWideUndrivenNetBits(f, "tri0", false);
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved_strength.s0_hi, Strength::kPull);
}

TEST(Tri0Tri1NetStrengths, DeclaredTri1WideVectorUndrivenAllBitsOne) {
  SimFixture f;
  auto* w = ExpectWideUndrivenNetBits(f, "tri1", true);
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->resolved_strength.s1_hi, Strength::kPull);
}

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

TEST(Tri0Tri1NetStrengths, SignalThroughASwitchOverridesThePull) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  tri0 t0;\n"
      "  tri1 t1;\n"
      "  assign a = 1'b1;\n"
      "  assign b = 1'b0;\n"
      "  tran (a, t0);\n"
      "  tran (b, t1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* t0 = f.ctx.FindNet("t0");
  auto* t1 = f.ctx.FindNet("t1");
  ASSERT_NE(t0, nullptr);
  ASSERT_NE(t1, nullptr);
  EXPECT_EQ(t0->resolved->value.ToUint64() & 0x1, 1u);
  EXPECT_EQ(t0->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(t0->resolved_strength.s0_hi, Strength::kHighz);
  EXPECT_EQ(t1->resolved->value.ToUint64() & 0x1, 0u);
  EXPECT_EQ(t1->resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_EQ(t1->resolved_strength.s1_hi, Strength::kHighz);
}

TEST(Tri0Tri1NetStrengths, AnExplicitDataTypeKeepsThePullStrength) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  tri0 logic a;\n"
      "  tri1 logic [3:0] b;\n"
      "  tri0 logic [2:0] c;\n"
      "  initial #1 $display(\"%v %v %v %v\", a, b[3], b[0], c[1]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Pu0 Pu1 Pu1 Pu0\n");
}

TEST(Tri0Tri1NetStrengths, AnUndrivenNetIsPullInEveryPlaceItIsDeclared) {
  for (auto place :
       {NetDeclarationPlace::kCompilationUnit, NetDeclarationPlace::kInterface,
        NetDeclarationPlace::kGenerate, NetDeclarationPlace::kProgram}) {
    EXPECT_EQ(NetStrengthDeclaredIn(place, "tri0 n;"), "Pu0\n")
        << static_cast<int>(place);
    EXPECT_EQ(NetStrengthDeclaredIn(place, "tri1 n;"), "Pu1\n")
        << static_cast<int>(place);
  }
}

}  // namespace
