#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LogicValuesSim, FourBasicValuesEncodeDistinctly) {
  // §6.3.1 canonical encoding (LRM Figure 38-8): 0=(0,0), 1=(1,0),
  // x=(aval=1,bval=1), z=(aval=0,bval=1).
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
  // §6.3.1: 1 represents a true condition and 0 represents a false condition.
  Arena arena;
  auto one = MakeLogic4VecVal(arena, 1, 1);
  auto zero = MakeLogic4VecVal(arena, 1, 0);
  EXPECT_TRUE(one.IsKnown());
  EXPECT_TRUE(zero.IsKnown());
  EXPECT_TRUE(one.IsTruthy());
  EXPECT_FALSE(zero.IsTruthy());
}

TEST(LogicValuesSim, UnknownAndHighZAreNeitherKnownNorTrue) {
  // §6.3.1: x is an unknown value and z is a high-impedance state; neither is
  // a definite 0 or 1, so each is unknown and does not yield a true condition.
  Arena arena;
  auto vx = MakeLogic4Vec(arena, 1);
  vx.words[0].aval = 1;
  vx.words[0].bval = 1;  // x encodes as aval=1, bval=1
  auto vz = MakeLogic4Vec(arena, 1);
  vz.words[0].bval = 1;  // z encodes as aval=0, bval=1
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

// The synthetic cases above exercise the value encoding directly. The rules in
// §6.3.1 that hinge on how a value is produced -- a 4-state object
// independently holding each of the four basic values, a z encountered in an
// expression, and a 2-state object being unable to store x/z -- are observed
// below by driving real source (a logic/bit declaration plus a literal
// assignment) through the full parse/elaborate/lower/run pipeline and reading
// the resulting 4-state value.

// §6.3.1: all four basic values can be held, and every bit of a 4-state vector
// can independently be one of them. Built from a real declaration + literal so
// the value flows through the production storage path, not a hand-set word.
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
  // MSB-first rendering: bit3=1, bit2=x, bit1=0, bit0=z, each held distinctly.
  EXPECT_EQ(var->value.ToString(), "1x0z");
  EXPECT_FALSE(var->value.IsKnown());
}

// §6.3.1: a z encountered in an expression usually has the same effect as an x.
// A z and an x are each driven through the same bitwise-AND expression; the two
// results must agree and both must be unknown.
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

// §6.3.1 (negative/contrast): a 2-state type stores only 0 or 1 in each bit, so
// assigning x/z to a bit vector cannot preserve those values -- they collapse
// to a known result -- whereas the same literal in a 4-state logic vector is
// kept.
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
  // 2-state: x/z are not storable, so both bits become known (0).
  EXPECT_TRUE(b->value.IsKnown());
  EXPECT_EQ(b->value.ToString(), "00");
  // 4-state: the same literal keeps the unknown and high-impedance bits.
  EXPECT_FALSE(l->value.IsKnown());
  EXPECT_EQ(l->value.ToString(), "xz");
}

// §6.3.1: 1 represents a true condition. Distinct input form from holding a
// value as stored data -- here the value is produced from a literal and used in
// a condition; the true branch must be taken. Driven through the full pipeline
// so production condition evaluation, not IsTruthy() in isolation, is observed.
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
  EXPECT_EQ(r->value.ToUint64(), 0xAAu);  // true branch taken
}

// §6.3.1: 0 represents a false condition. Same condition position, produced
// from a literal 0; the else branch must be taken.
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
  EXPECT_EQ(r->value.ToUint64(), 0x55u);  // false branch taken
}

// §6.3.1 (negative): x is unknown and z is high-impedance -- neither is a
// definite 1, so neither yields a true condition. Both must take the else
// branch, the rejecting counterpart to a known 1 as a condition.
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

}  // namespace
