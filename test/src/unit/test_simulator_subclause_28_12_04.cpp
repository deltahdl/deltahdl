#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "model_strength.h"
#include "model_val4.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

static Net* RunAndFindNetW(SimFixture& f, const char* src) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindNet("w");
}

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
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
  EXPECT_FALSE(net->resolved_strength.IsAmbiguous());
}

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
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_FALSE(net->resolved_strength.IsAmbiguous());
}

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
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_EQ(net->resolved_strength.s1_hi, Strength::kStrong);
}

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
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kStrong);
}

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
  EXPECT_EQ(var->value.ToUint64(), 0b1000u);
}

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
  EXPECT_EQ(var->value.ToUint64(), 0b1110u);
}

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
  EXPECT_EQ(zero_var->value.ToUint64(), 0u);

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
  EXPECT_EQ(x_var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(x_var->value.words[0].bval & 1u, 1u);
}

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
  EXPECT_EQ(one_var->value.ToUint64(), 1u);

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
  EXPECT_EQ(x_var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(x_var->value.words[0].bval & 1u, 1u);
}

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
  EXPECT_EQ(var->value.words[0].aval & 1u, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

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
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(WiredLogicPipeline, WandNetDeclInitializerAndsWithAssign) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wand w = 1'b1;\n"
                            "  assign w = 1'b0;\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

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
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_EQ(net->resolved_strength.s0_hi, Strength::kPull);
  EXPECT_EQ(net->resolved_strength.s0_lo, Strength::kPull);
}

TEST(WiredLogicPipeline, WorGateOutputDriversOrToOne) {
  SimFixture f;
  Net* net = RunAndFindNetW(f,
                            "module t;\n"
                            "  wor w;\n"
                            "  wire a = 1'b1, b = 1'b1;\n"
                            "  wire c = 1'b0, d = 1'b1;\n"
                            "  and g0(w, a, b);\n"
                            "  and g1(w, c, d);\n"
                            "endmodule\n");
  ASSERT_NE(net, nullptr);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(WiredLogicPipeline, WandThroughTwoInstancesOutputPortsReResolves) {
  SimFixture f;
  auto out = RunCapture(
      "module d1 (output w, input a);\n"
      "  buf g (w, a);\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  logic a = 1, b = 0;\n"
      "  d1 x (w, a);\n"
      "  d1 y (w, b);\n"
      "  initial begin\n"
      "    #1 $display(\"w=%b\", w);\n"
      "    b = 1;\n"
      "    #1 $display(\"w=%b\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "w=0\nw=1\n");
}

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

static StrengthSignal UnknownValueSignal(StrengthLevel level) {
  StrengthSignal s;
  s.value = Val4::kX;
  s.strength0_hi = level;
  s.strength0_lo = level;
  s.strength1_hi = level;
  s.strength1_lo = level;
  return s;
}

TEST(WiredLogicModel, WiredAndOfOppositeValuesAtEqualLevelGivesZero) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kStrong);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kAnd);

  EXPECT_EQ(r.value, Val4::kV0);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kHighz);
}

TEST(WiredLogicModel, WiredOrOfOppositeValuesAtEqualLevelGivesOne) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kStrong);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kOr);

  EXPECT_EQ(r.value, Val4::kV1);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kHighz);
}

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

TEST(WiredLogicModel, WiredAndOfStrongerZeroWithWeakerOneGivesZero) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kPull);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kAnd);

  EXPECT_EQ(r.value, Val4::kV0);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kHighz);
}

TEST(WiredLogicModel, WiredOrOfStrongerZeroWithWeakerOneGivesZero) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnambiguousSignal(Val4::kV1, StrengthLevel::kPull);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kOr);

  EXPECT_EQ(r.value, Val4::kV0);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kHighz);
}

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

TEST(WiredLogicModel, WiredAndOfOneWithUnknownAtEqualLevelGivesUnknown) {
  auto a = UnambiguousSignal(Val4::kV1, StrengthLevel::kStrong);
  auto b = UnknownValueSignal(StrengthLevel::kStrong);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kAnd);

  EXPECT_EQ(r.value, Val4::kX);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
}

TEST(WiredLogicModel, WiredOrOfZeroWithUnknownAtEqualLevelGivesUnknown) {
  auto a = UnambiguousSignal(Val4::kV0, StrengthLevel::kStrong);
  auto b = UnknownValueSignal(StrengthLevel::kStrong);

  auto r = CombineWithWiredLogic(a, b, ModelWiredLogicKind::kOr);

  EXPECT_EQ(r.value, Val4::kX);
  EXPECT_EQ(r.strength0_hi, StrengthLevel::kStrong);
  EXPECT_EQ(r.strength1_hi, StrengthLevel::kStrong);
}

TEST(WiredLogicPipeline, AmbiguousDriverCombinesOverAllLevels) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire s1; wand wa; wor wo;\n"
      "  logic zero = 0, g = 1'bx;\n"
      "  pmos p1 (s1, zero, g);\n"
      "  buf (pull1, pull0) b1 (s1, zero);\n"
      "  pmos p2 (wa, zero, g);\n"
      "  buf (pull1, pull0) b2 (wa, zero);\n"
      "  pullup (wa);\n"
      "  pmos p3 (wo, zero, g);\n"
      "  buf (pull1, pull0) b3 (wo, zero);\n"
      "  pullup (wo);\n"
      "  initial begin\n"
      "    #1 $display(\"s1=%b %v\", s1, s1);\n"
      "    $display(\"wa=%b %v wo=%b %v\", wa, wa, wo, wo);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "s1=0 650\n"
            "wa=0 650 wo=x 65X\n");
}

}  // namespace
