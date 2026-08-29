#include <gtest/gtest.h>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "model_strength.h"
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
//
// The WiredLogicModel tests at the end of this file cover
// CombineWithWiredLogic in lib/cpp/test_models/model_strength.h, which nothing
// called before issue #3417 and which therefore stated a reading of §28.12.4
// that no run evaluated. They claim five things the clause decides about
// combining two signals on a wand, triand, wor or trior net. The result value
// is the value an `and` gate or an `or` gate gives for the two signal values
// when the two signals carry one strength level each and carry the same level.
// The result strength is that shared level. Where the two levels differ, the
// signal at the stronger level is the whole result, whichever logic function
// the net type names. Where an operand spans several strength levels, both of
// Figure 28-25's charts are read at every pair of levels and the rows are taken
// together as one range, which can reach both sides of the scale and give a
// result of value x where neither operand had one. An x operand is itself a
// signal holding cells on both sides, and an `and` gate or an `or` gate hands
// back x for it at equal strength. Each test quotes the sentence or the Figure
// 28-25 chart row it rests on.
//
// Issue #3423 is what the last three of those tests close.
// CombineWithWiredLogic read each operand's _hi field alone, so it collapsed an
// operand spanning several strength levels to its top level and never formed
// Figure 28-25's union of the chart rows. It answered an x operand by the
// complement of the case it tested for. ModelWiredLogicKind also carried a
// kNone enumerator that fell through to the or arm, and it now declares kAnd
// and kOr and nothing else.
//
// model_strength.h records a strength signal as a span of Figure 28-2's sixteen
// cells. A side is occupied when its _hi is above kHighz, and it then holds
// every level from its _lo up to its _hi. UnambiguousSignal below builds the
// one-cell form that a driver of known value and one strength level puts on a
// net, so no case here repeats the four strength fields.

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

// The signal one driver of known value and one strength level puts on a net.
// model_strength.h holds an unambiguous signal as one cell of Figure 28-2's
// scale, so the level is written to both _lo and _hi on the side the value
// names and kHighz is left on the other side. A three-field aggregate
// initializer leaves both _lo at kHighz instead, which builds a signal
// occupying its side all the way down to high impedance.
static StrengthSignal UnambiguousSignal(Val4 value, StrengthLevel level) {
  StrengthSignal s;
  s.value = value;
  if (value == Val4::kV0) {
    s.strength0_hi = level;
    s.strength0_lo = level;
  } else {
    s.strength1_hi = level;
    s.strength1_lo = level;
  }
  return s;
}

// The signal one driver of value x and one strength level puts on a net: that
// level on the strength0 side and on the strength1 side at once.
// model_strength.h reads a signal holding cells on both sides as the value x.
static StrengthSignal UnknownValueSignal(StrengthLevel level) {
  StrengthSignal s;
  s.value = Val4::kX;
  s.strength0_hi = level;
  s.strength0_lo = level;
  s.strength1_hi = level;
  s.strength1_lo = level;
  return s;
}

// §28.12.4: "The combination of the signals in Figure 28-24, using wired and
// logic, produces a result with the same value as the result produced by an
// and gate with the value of the two signals as its inputs." Figure 28-24
// combines a value 0 at strength level 6 (St0) with a value 1 at strength
// level 6 (St1) and prints "wired AND logic value result: 0". The level of the
// result is fixed by "The strength of the result is the same as the strength
// of the combined signals in both cases". model_strength.h records an
// unambiguous signal as its level on the side its value names and kHighz on
// the other side, which is what the strength1_hi assertion reads.
TEST(WiredLogicModel, WiredAndOfOppositeValuesAtEqualLevelGivesZero) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kStrong);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kAnd);

  EXPECT_EQ(r.value, Val4::kV0);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kHighz);
}

// §28.12.4: "The combination of signals using wired or logic produces a result
// with the same value as the result produced by an or gate with the values of
// the two signals as its inputs." Figure 28-24 prints "wired OR logic value
// result: 1" for the same two signals the test above combines, so the net type
// and not the operands decides which of the two results a run gives. "The
// strength of the result is the same as the strength of the combined signals
// in both cases" fixes the level at 6 (St1) here as it does there.
TEST(WiredLogicModel, WiredOrOfOppositeValuesAtEqualLevelGivesOne) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kStrong);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kOr);

  EXPECT_EQ(r.value, Val4::kV1);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kHighz);
}

// §28.12.4: "If the value of the upper signal changes so that both signals in
// Figure 28-24 possess a value 1, then the results of both types of logic have
// a value 1." Figure 28-24 gives its two signals one strength level each and
// gives them the same level, and "The strength of the result is the same as
// the strength of the combined signals in both cases" fixes the result at that
// level. The level here is 3 (We1) rather than Figure 28-24's 6, the sentence
// naming no particular level.
TEST(WiredLogicModel, WiredLogicOfLikeOnesGivesOneUnderBothKinds) {
  auto a = UnambiguousSignal(Val4::kV1, StrengthLevel::kWeak);
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kWeak);

  auto r_and = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kAnd);
  auto r_or = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kOr);

  EXPECT_EQ(r_and.value, Val4::kV1);
  EXPECT_EQ(r_and.strength1_hi, StrengthLevel::kWeak);
  EXPECT_EQ(r_and.strength0_hi, StrengthLevel::kHighz);
  EXPECT_EQ(r_or.value, Val4::kV1);
  EXPECT_EQ(r_or.strength1_hi, StrengthLevel::kWeak);
  EXPECT_EQ(r_or.strength0_hi, StrengthLevel::kHighz);
}

// §28.12.4: "When ambiguous strength signals combine in wired logic, it is
// necessary to consider the results of all combinations of each of the
// strength levels in the first signal with each of the strength levels in the
// second signal, as shown in Figure 28-25." The second row of Figure 28-25's
// and chart pairs strength 6 value 0 with strength 5 value 1 and gives
// strength 6 value 0. A row of that chart combines one level with one level,
// so it decides two unambiguous signals as well as two levels drawn from
// ambiguous ones.
TEST(WiredLogicModel, WiredAndOfStrongerZeroWithWeakerOneGivesZero) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kPull);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kAnd);

  EXPECT_EQ(r.value, Val4::kV0);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kHighz);
}

// §28.12.4, Figure 28-25: the second row of the or chart pairs strength 6
// value 0 with strength 5 value 1 and gives strength 6 value 0, the same
// result the and chart's second row gives. So the stronger level carries its
// own value into the result even under or logic, where an or gate of 0 and 1
// gives 1. These are the operands the test above uses, and the two tests
// together are what distinguishes applying the logic function at every pair of
// levels from applying it only where the levels are equal.
TEST(WiredLogicModel, WiredOrOfStrongerZeroWithWeakerOneGivesZero) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kPull);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kOr);

  EXPECT_EQ(r.value, Val4::kV0);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kHighz);
}

// §28.12.4's Figure 28-25 read whole, under and logic. Signal 1 is a value 0
// holding strength levels 6 and 5 (St0 through Pu0), signal 2 is a value 1
// holding strength level 5 (Pu1), and the two rows of the and chart give
// strength 5 value 0 and strength 6 value 0. The figure draws that result as a
// value 0 spanning levels 5 through 6 with the whole strength1 half of the
// scale empty, which the four strength assertions read. The lower bound is Pu0
// and not high impedance, because level 5 is the weakest level any chart row
// returns and the figure's arrow starts there.
TEST(WiredLogicModel, WiredAndOfAmbiguousZeroRangeWithWeakerOneKeepsRange) {
  StrengthSignal a;
  a.value = Val4::kV0;
  a.strength0_lo = StrengthLevel::kPull;
  a.strength0_hi = StrengthLevel::kStrong;
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kPull);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kAnd);

  EXPECT_EQ(r.value, Val4::kV0);
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kPull);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kHighz);
}

// §28.12.4's Figure 28-25 read whole, under or logic, on the operands the test
// above combines. The or chart gives strength 5 value 1 for its first row and
// strength 6 value 0 for its second, and the figure draws the result as one
// arrow running from St0 across to Pu1. That range holds cells of value 0 and
// cells of value 1, so the result has the value x. It reaches St0 on the
// strength0 side and Pu1 on the strength1 side, and it covers high impedance
// on both sides because it crosses the middle of Figure 28-2's scale, which is
// what the two _lo assertions read. Neither operand has the value x and the
// result does, so this case is the one that shows the chart's rows being taken
// together as one range rather than one row being answered alone.
TEST(WiredLogicModel,
     WiredOrOfAmbiguousZeroRangeWithWeakerOneCrossesToUnknown) {
  StrengthSignal a;
  a.value = Val4::kV0;
  a.strength0_lo = StrengthLevel::kPull;
  a.strength0_hi = StrengthLevel::kStrong;
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kPull);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kOr);

  EXPECT_EQ(r.value, Val4::kX);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength0_lo, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength1_lo, StrengthLevel::kHighz);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kPull);
}

// §28.12.4 fixes the result value as "the same value as the result produced by
// an and gate with the value of the two signals as its inputs", and an and
// gate of 1 and x gives x. The two signals carry strength level 6 here, so
// "The strength of the result is the same as the strength of the combined
// signals in both cases" puts the result at level 6 on both sides of the
// scale. The x operand is built as a signal holding cells on the strength0
// side and on the strength1 side, which is the form model_strength.h reads as
// the value x.
TEST(WiredLogicModel, WiredAndOfOneWithUnknownAtEqualLevelGivesUnknown) {
  auto a = UnambiguousSignal(Val4::kV1, StrengthLevel::kStrong);
  auto b = UnknownValueSignal(StrengthLevel::kStrong);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kAnd);

  EXPECT_EQ(r.value, Val4::kX);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
}

// §28.12.4 fixes the result value as "the same value as the result produced by
// an or gate with the values of the two signals as its inputs", and an or gate
// of 0 and x gives x. This is the or counterpart of the test above, and the
// pair is what separates the two logic functions on an x operand: neither
// value is controlling for its own gate here, so neither result is decided by
// the known operand. "The strength of the result is the same as the strength
// of the combined signals in both cases" puts this result at level 6 as well.
TEST(WiredLogicModel, WiredOrOfZeroWithUnknownAtEqualLevelGivesUnknown) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnknownValueSignal(StrengthLevel::kStrong);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kOr);

  EXPECT_EQ(r.value, Val4::kX);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
}

}  // namespace
