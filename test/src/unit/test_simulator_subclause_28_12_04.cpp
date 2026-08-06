#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §28.12.4 Wired logic net types.
//
// The net types wand, triand, wor, and trior resolve conflicts between multiple
// drivers of the same strength by treating the driver values as inputs of a
// logic function: wand/triand apply AND, wor/trior apply OR. The result carries
// the strength of the combined signals. These tests build the net type from a
// real net declaration (§6.7.1) and the competing drivers from real
// continuous-assignment source (§28.11), then elaborate, lower, and run, so the
// resolved value and strength are observed exactly as the production resolver
// computes them -- not from a hand-assembled Net. A plain continuous assignment
// carries the default strong/strong strength, so the two drivers below always
// have equal strength, which is the same-strength case the rule governs.

// Elaborates, lowers, and runs `src`, then returns the settled net named "w".
static Net* RunAndFindNetW(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindNet("w");
}

// Claim A + B (wand -> AND): two equal-strength drivers with conflicting values
// on a wand net resolve to the AND of the values.
TEST(WiredLogicPipeline, WandSameStrengthConflictAndsToZero) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wand w;\n"
                            "  assign w = 1'b1;\n"
                            "  assign w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);  // 1 AND 0 == 0
  // Claim C: the result carries the strength of the combined signals (strong).
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_FALSE(net->resolved_strength.IsAmbiguous());
}

// Claim A + B (wor -> OR): two equal-strength drivers with conflicting values
// on a wor net resolve to the OR of the values.
TEST(WiredLogicPipeline, WorSameStrengthConflictOrsToOne) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wor w;\n"
                            "  assign w = 1'b1;\n"
                            "  assign w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);  // 1 OR 0 == 1
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_FALSE(net->resolved_strength.IsAmbiguous());
}

// Claim A + B (triand -> AND): triand shares wand's logic-function resolution.
TEST(WiredLogicPipeline, TriandSameStrengthConflictAndsToZero) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  triand w;\n"
                            "  assign w = 1'b1;\n"
                            "  assign w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
}

// Claim A + B (trior -> OR): trior shares wor's logic-function resolution.
TEST(WiredLogicPipeline, TriorSameStrengthConflictOrsToOne) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  trior w;\n"
                            "  assign w = 1'b1;\n"
                            "  assign w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kStrong);
}

// Claim C (Figure 28-24, like values): a wand of two 1-valued drivers gives 1;
// the strength of the result is the combined driver strength.
TEST(WiredLogicPipeline, WandLikeOnesGiveOneAtCombinedStrength) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wand w;\n"
                            "  assign w = 1'b1;\n"
                            "  assign w = 1'b1;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);  // 1 AND 1 == 1
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kStrong);
}

// Claim C (Figure 28-24, like values): a wor of two 0-valued drivers gives 0.
TEST(WiredLogicPipeline, WorLikeZerosGiveZeroAtCombinedStrength) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wor w;\n"
                            "  assign w = 1'b0;\n"
                            "  assign w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);  // 0 OR 0 == 0
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
}

// Claim B, vector operand: the logic function is applied independently per bit,
// so on a multi-bit wand each bit is the AND of the two drivers' bits.
TEST(WiredLogicPipeline, WandVectorAndsPerBit) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wand [3:0] w;\n"
                            "  assign w = 4'b1100;\n"
                            "  assign w = 4'b1010;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b1000u);  // per-bit AND
}

// Claim B, vector operand: per-bit OR on a wor net.
TEST(WiredLogicPipeline, WorVectorOrsPerBit) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wor [3:0] w;\n"
                            "  assign w = 4'b1100;\n"
                            "  assign w = 4'b1010;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b1110u);  // per-bit OR
}

// Claim B, x operand under AND: wand treats x as a logic input, so 0 AND x is a
// controlling 0 while 1 AND x is x.
TEST(WiredLogicPipeline, WandZeroDominatesXButOneYieldsX) {
  SimFixture f0;
  Net* zero_net = RunAndFindNetW(f0,
                                 "module t;\n"
                                 "  wand w;\n"
                                 "  assign w = 1'b0;\n"
                                 "  assign w = 1'bx;\n"
                                 "endmodule\n");
  ASSERT_NE(zero_net, nullptr);
  auto* zero_var = f0.ctx.FindVariable("w");
  ASSERT_NE(zero_var, nullptr);
  EXPECT_EQ(zero_var->value.ToUint64(), 0u);  // 0 AND x == 0

  SimFixture f1;
  Net* x_net = RunAndFindNetW(f1,
                              "module t;\n"
                              "  wand w;\n"
                              "  assign w = 1'b1;\n"
                              "  assign w = 1'bx;\n"
                              "endmodule\n");
  ASSERT_NE(x_net, nullptr);
  auto* x_var = f1.ctx.FindVariable("w");
  ASSERT_NE(x_var, nullptr);
  EXPECT_EQ(x_var->value.words[0].aval & 1u, 1u);  // 1 AND x == x
  EXPECT_EQ(x_var->value.words[0].bval & 1u, 1u);
}

// Claim B, x operand under OR: wor's 1 is controlling (1 OR x == 1) while 0 OR
// x is x.
TEST(WiredLogicPipeline, WorOneDominatesXButZeroYieldsX) {
  SimFixture f1;
  Net* one_net = RunAndFindNetW(f1,
                                "module t;\n"
                                "  wor w;\n"
                                "  assign w = 1'b1;\n"
                                "  assign w = 1'bx;\n"
                                "endmodule\n");
  ASSERT_NE(one_net, nullptr);
  auto* one_var = f1.ctx.FindVariable("w");
  ASSERT_NE(one_var, nullptr);
  EXPECT_EQ(one_var->value.ToUint64(), 1u);  // 1 OR x == 1

  SimFixture f0;
  Net* x_net = RunAndFindNetW(f0,
                              "module t;\n"
                              "  wor w;\n"
                              "  assign w = 1'b0;\n"
                              "  assign w = 1'bx;\n"
                              "endmodule\n");
  ASSERT_NE(x_net, nullptr);
  auto* x_var = f0.ctx.FindVariable("w");
  ASSERT_NE(x_var, nullptr);
  EXPECT_EQ(x_var->value.words[0].aval & 1u, 1u);  // 0 OR x == x
  EXPECT_EQ(x_var->value.words[0].bval & 1u, 1u);
}

// Negative form: the same equal-strength conflicting drivers on a plain wire
// (not a wired-logic net type) are NOT combined by a logic function -- they
// collide to x. This confirms the AND/OR resolution is specific to the wand /
// wor / triand / trior net types §28.12.4 names.
TEST(WiredLogicPipeline, PlainWireDoesNotApplyLogicFunction) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wire w;\n"
                            "  assign w = 1'b1;\n"
                            "  assign w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);  // conflict -> x, not AND/OR
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// Claim A, three drivers: the logic function folds across every same-strength
// driver, so a single controlling 0 forces a wand result to 0.
TEST(WiredLogicPipeline, WandFoldsAcrossThreeDrivers) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wand w;\n"
                            "  assign w = 1'b1;\n"
                            "  assign w = 1'b1;\n"
                            "  assign w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);  // 1 AND 1 AND 0 == 0
}

// Claim A + B, driver produced by a net-declaration assignment (§6.7.1): a wand
// net declared with an initializer is itself a continuous driver, occupying a
// different syntactic position than a standalone `assign`. It combines with a
// second driver of equal (default) strength under the wired-AND rule. Built
// from that dependency's real source so the net-decl-initializer driver is
// produced by the pipeline, not stubbed.
TEST(WiredLogicPipeline, WandNetDeclInitializerAndsWithAssign) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wand w = 1'b1;\n"    // net-decl driver: 1
                            "  assign w = 1'b0;\n"  // cont-assign driver: 0
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);  // 1 AND 0 == 0
}

// Claim A + C, drivers produced by drive-strength continuous assignments
// (§28.11): two drivers carrying the SAME explicit strength conflict, so the
// wand net ANDs their values and the result keeps that shared strength (pull).
// Exercises §28.11's real drive-strength syntax feeding §28.12.4's
// same-strength resolution, distinct from the default-strong drivers used
// elsewhere.
TEST(WiredLogicPipeline, WandExplicitSameDriveStrengthAndsAtThatStrength) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wand w;\n"
                            "  assign (pull0, pull1) w = 1'b1;\n"
                            "  assign (pull0, pull1) w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);  // 1 AND 0 == 0
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net->resolved_strength.s0_lo, Strength::kPull);
}

// Claim A + B, drivers produced by gate primitives (§28.4) feeding a wired net
// (§28.11): the net resolves its drivers regardless of how they are produced.
// Two `and` gate outputs of equal (default strong) strength carrying
// conflicting values drive a wor net, which ORs them. Gates and operands are
// built from real source and run end to end.
TEST(WiredLogicPipeline, WorGateOutputDriversOrToOne) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wor w;\n"
                            "  wire a = 1'b1, b = 1'b1;\n"  // and -> 1
                            "  wire c = 1'b0, d = 1'b1;\n"  // and -> 0
                            "  and g0(w, a, b);\n"          // strong 1 driver
                            "  and g1(w, c, d);\n"          // strong 0 driver
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);  // 1 OR 0 == 1
}

// Claim D (Figure 28-25): when ambiguous-strength signals combine in wired
// logic, every strength level of the first signal is paired with every strength
// level of the second and the logic function is applied per pair. This is a
// pure resolver helper over strength ranges: its result is defined entirely by
// the two NetStrength operands and does not depend on how those ranges were
// produced, so it is exercised directly at the resolver stage.
TEST(WiredLogicAmbig, AndPairwiseAcrossStrengthRanges) {
  NetStrength a;
  a.s0_lo = Strength::kPull;
  a.s0_hi = Strength::kStrong;
  NetStrength b;
  b.s1_lo = Strength::kLarge;
  b.s1_hi = Strength::kPull;

  auto r = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);

  EXPECT_EQ(r.s0_lo, Strength::kPull);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
  EXPECT_EQ(r.s1_lo, Strength::kHighz);
}

TEST(WiredLogicAmbig, OrPairwiseAcrossStrengthRanges) {
  NetStrength a;
  a.s0_lo = Strength::kPull;
  a.s0_hi = Strength::kStrong;
  NetStrength b;
  b.s1_lo = Strength::kLarge;
  b.s1_hi = Strength::kPull;

  auto r = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kOr);

  EXPECT_EQ(r.s0_lo, Strength::kPull);
  EXPECT_EQ(r.s0_hi, Strength::kStrong);
  EXPECT_EQ(r.s1_lo, Strength::kPull);
  EXPECT_EQ(r.s1_hi, Strength::kPull);
}

TEST(WiredLogicAmbig, LikeValuesKeepSingleSideUnionedRange) {
  NetStrength a;
  a.s1_lo = Strength::kWeak;
  a.s1_hi = Strength::kPull;
  NetStrength b;
  b.s1_lo = Strength::kLarge;
  b.s1_hi = Strength::kStrong;

  auto r_and = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);
  auto r_or = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kOr);

  EXPECT_EQ(r_and.s0_hi, Strength::kHighz);
  EXPECT_EQ(r_and.s1_lo, Strength::kLarge);
  EXPECT_EQ(r_and.s1_hi, Strength::kStrong);
  EXPECT_EQ(r_or.s0_hi, Strength::kHighz);
  EXPECT_EQ(r_or.s1_lo, Strength::kLarge);
  EXPECT_EQ(r_or.s1_hi, Strength::kStrong);
}

TEST(WiredLogicAmbig, UnambigInputsAgreeWithPerPairRule) {
  NetStrength a;
  a.s0_lo = Strength::kStrong;
  a.s0_hi = Strength::kStrong;
  NetStrength b;
  b.s1_lo = Strength::kStrong;
  b.s1_hi = Strength::kStrong;

  auto r_and = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);
  auto r_or = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kOr);

  EXPECT_EQ(r_and.s0_lo, Strength::kStrong);
  EXPECT_EQ(r_and.s0_hi, Strength::kStrong);
  EXPECT_EQ(r_and.s1_hi, Strength::kHighz);
  EXPECT_EQ(r_or.s1_lo, Strength::kStrong);
  EXPECT_EQ(r_or.s1_hi, Strength::kStrong);
  EXPECT_EQ(r_or.s0_hi, Strength::kHighz);
}

TEST(WiredLogicAmbig, AndProducesDualSidedRange) {
  NetStrength a;
  a.s0_lo = Strength::kPull;
  a.s0_hi = Strength::kPull;
  a.s1_lo = Strength::kStrong;
  a.s1_hi = Strength::kStrong;
  NetStrength b;
  b.s1_lo = Strength::kPull;
  b.s1_hi = Strength::kPull;

  auto r = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);

  EXPECT_EQ(r.s0_lo, Strength::kPull);
  EXPECT_EQ(r.s0_hi, Strength::kPull);
  EXPECT_EQ(r.s1_lo, Strength::kStrong);
  EXPECT_EQ(r.s1_hi, Strength::kStrong);
  EXPECT_FALSE(r.IsAmbiguous());
}

TEST(WiredLogicAmbig, EmptyInputProducesEmptyRange) {
  NetStrength a;
  NetStrength b;
  b.s0_lo = Strength::kPull;
  b.s0_hi = Strength::kPull;

  auto r = CombineWiredLogicAmbiguous(a, b, WiredLogicKind::kAnd);

  EXPECT_EQ(r.s0_hi, Strength::kHighz);
  EXPECT_EQ(r.s1_hi, Strength::kHighz);
}

}  // namespace
