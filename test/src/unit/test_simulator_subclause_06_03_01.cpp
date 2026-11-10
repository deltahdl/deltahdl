#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LogicValuesSim, FourBasicValuesEncodeDistinctly) {
  Logic4Word v0{0, 0};
  Logic4Word v1{1, 0};
  Logic4Word vx{1, 1};
  Logic4Word vz{0, 1};
  EXPECT_TRUE(v0.IsZero());
  EXPECT_TRUE(v1.IsOne());
  EXPECT_TRUE(v0.IsKnown());
  EXPECT_TRUE(v1.IsKnown());
  EXPECT_FALSE(vx.IsKnown());
  EXPECT_FALSE(vz.IsKnown());
}

TEST(LogicValuesSim, KnownOneIsTrueConditionAndKnownZeroIsFalseCondition) {
  Arena arena;
  auto one = MakeLogic4VecVal(arena, 1, 1);
  auto zero = MakeLogic4VecVal(arena, 1, 0);
  EXPECT_TRUE(one.IsKnown());
  EXPECT_TRUE(zero.IsKnown());
  EXPECT_TRUE(one.IsTruthy());
  EXPECT_FALSE(zero.IsTruthy());
}

TEST(LogicValuesSim, UnknownAndHighZAreNeitherKnownNorTrue) {
  Arena arena;
  auto vx = MakeLogic4Vec(arena, 1);
  vx.words[0].aval = 1;
  vx.words[0].bval = 1;
  auto vz = MakeLogic4Vec(arena, 1);
  vz.words[0].bval = 1;
  EXPECT_FALSE(vx.IsKnown());
  EXPECT_FALSE(vz.IsKnown());
  EXPECT_FALSE(vx.IsTruthy());
  EXPECT_FALSE(vz.IsTruthy());
}

TEST(LogicValuesSim, ZeroComplementsToOne) {
  Logic4Word v0{0, 0};
  auto r = Logic4Not(v0);
  EXPECT_EQ(r.aval & 1u, 1u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

TEST(LogicValuesSim, OneComplementsToZero) {
  Logic4Word v1{1, 0};
  auto r = Logic4Not(v1);
  EXPECT_EQ(r.aval & 1u, 0u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

TEST(LogicValuesSim, ZBehavesLikeXUnderBitwiseNot) {
  Logic4Word vz{0, 1};
  Logic4Word vx{1, 1};
  auto rz = Logic4Not(vz);
  auto rx = Logic4Not(vx);
  EXPECT_EQ(rz.aval, rx.aval);
  EXPECT_EQ(rz.bval, rx.bval);
}

TEST(LogicValuesSim, ZAndZeroCollapsesToZero) {
  Logic4Word v0{0, 0};
  Logic4Word vz{0, 1};
  auto r = Logic4And(vz, v0);
  EXPECT_EQ(r.aval & 1u, 0u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

TEST(LogicValuesSim, ZBehavesLikeXUnderBitwiseOrWithZero) {
  Logic4Word v0{0, 0};
  Logic4Word vz{0, 1};
  Logic4Word vx{1, 1};
  auto rz = Logic4Or(vz, v0);
  auto rx = Logic4Or(vx, v0);
  EXPECT_EQ(rz.aval & 1u, rx.aval & 1u);
  EXPECT_EQ(rz.bval & 1u, rx.bval & 1u);
  EXPECT_EQ(rz.bval & 1u, 1u);
}

TEST(LogicValuesSim, ZOrOneCollapsesToOne) {
  Logic4Word v1{1, 0};
  Logic4Word vz{0, 1};
  auto r = Logic4Or(vz, v1);
  EXPECT_EQ(r.aval & 1u, 1u);
  EXPECT_EQ(r.bval & 1u, 0u);
}

TEST(LogicValuesSim, ZBehavesLikeXUnderBitwiseXor) {
  Logic4Word v1{1, 0};
  Logic4Word vz{0, 1};
  Logic4Word vx{1, 1};
  auto rz = Logic4Xor(vz, v1);
  auto rx = Logic4Xor(vx, v1);
  EXPECT_EQ(rz.aval & 1u, rx.aval & 1u);
  EXPECT_EQ(rz.bval & 1u, rx.bval & 1u);
  EXPECT_EQ(rz.bval & 1u, 1u);
}

TEST(LogicValuesSim, DeclaredLogicVectorHoldsAllFourValuesFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial v = 4'b1x0z;\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "1x0z");
  EXPECT_FALSE(var->value.IsKnown());
}

TEST(LogicValuesSim, HighImpedanceInExpressionBehavesLikeUnknownFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic zin, xin, rz, rx;\n"
      "  initial begin\n"
      "    zin = 1'bz;\n"
      "    xin = 1'bx;\n"
      "    rz = zin & 1'b1;\n"
      "    rx = xin & 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  auto* rz = f.ctx.FindVariable("rz");
  auto* rx = f.ctx.FindVariable("rx");
  ASSERT_NE(rz, nullptr);
  ASSERT_NE(rx, nullptr);
  EXPECT_EQ(rz->value.ToString(), "x");
  EXPECT_EQ(rz->value.ToString(), rx->value.ToString());
  EXPECT_FALSE(rz->value.IsKnown());
}

TEST(LogicValuesSim, TwoStateTypeCannotStoreUnknownOrHighImpedanceFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [1:0] b;\n"
      "  logic [1:0] l;\n"
      "  initial begin\n"
      "    b = 2'bxz;\n"
      "    l = 2'bxz;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  auto* b = f.ctx.FindVariable("b");
  auto* l = f.ctx.FindVariable("l");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(l, nullptr);
  EXPECT_TRUE(b->value.IsKnown());
  EXPECT_EQ(b->value.ToString(), "00");
  EXPECT_FALSE(l->value.IsKnown());
  EXPECT_EQ(l->value.ToString(), "xz");
}

TEST(LogicValuesSim, KnownOneDrivesTrueConditionFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    sel = 1'b1;\n"
      "    if (sel) r = 8'hAA; else r = 8'h55;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0xAAu);
}

TEST(LogicValuesSim, KnownZeroDrivesFalseConditionFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    sel = 1'b0;\n"
      "    if (sel) r = 8'hAA; else r = 8'h55;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0x55u);
}

TEST(LogicValuesSim, UnknownAndHighImpedanceDoNotDriveTrueConditionFromSource) {
  const char* tmpl =
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    sel = %s;\n"
      "    if (sel) r = 8'hAA; else r = 8'h55;\n"
      "  end\n"
      "endmodule\n";
  for (const char* lit : {"1'bx", "1'bz"}) {
    char src[512];
    snprintf(src, sizeof src, tmpl, lit);
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    LowerAndRun(design, f);
    auto* r = f.ctx.FindVariable("r");
    ASSERT_NE(r, nullptr);
    EXPECT_EQ(r->value.ToUint64(), 0x55u) << "condition literal: " << lit;
  }
}

TEST(LogicValuesSim,
     HighImpedanceAtAGateInputActsAsUnknownButAMosSwitchPassesIt) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  wire a, an, o, bf, n, x, nm, pm, cm;\n"
      "  assign a = 1'bz;\n"
      "  and  g1 (an, a, 1'b1);\n"
      "  or   g2 (o, a, 1'b0);\n"
      "  buf  g3 (bf, a);\n"
      "  not  g4 (n, a);\n"
      "  xor  g5 (x, a, 1'b0);\n"
      "  nmos m1 (nm, a, 1'b1);\n"
      "  pmos m2 (pm, a, 1'b0);\n"
      "  cmos m3 (cm, a, 1'b1, 1'b0);\n"
      "  initial #1 $display(\"%b %b %b %b %b %b %b %b\", an, o, bf, n, x, "
      "nm,\n"
      "                      pm, cm);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x x x x x z z z\n");
}

}  // namespace
