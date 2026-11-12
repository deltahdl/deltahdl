#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

#include "fixture_simulator.h"
#include "simulator/sva_engine_sampling.h"

using namespace delta;

namespace {

TEST(AssertionBooleanInterpretation, AllZeroKnownValueIsFalse) {
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0, 0));
}

TEST(AssertionBooleanInterpretation, AnyKnownNonZeroValueIsTrue) {
  EXPECT_TRUE(InterpretAssertionExprAsBoolean(1, 0));
  EXPECT_TRUE(InterpretAssertionExprAsBoolean(0xDEADBEEF, 0));
}

TEST(AssertionBooleanInterpretation, AnyUnknownBitForcesFalse) {
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0xFFFFFFFF, 0x1));
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0x1, 0x1));
  EXPECT_FALSE(InterpretAssertionExprAsBoolean(0x0, 0xFF));
}

TEST(AssertionBooleanInterpretation, MaximumKnownValueIsTrue) {
  EXPECT_TRUE(
      InterpretAssertionExprAsBoolean(std::numeric_limits<uint64_t>::max(), 0));
}

TEST(AssertionBooleanInterpretation, AllBitsUnknownIsFalse) {
  EXPECT_FALSE(
      InterpretAssertionExprAsBoolean(std::numeric_limits<uint64_t>::max(),
                                      std::numeric_limits<uint64_t>::max()));
  EXPECT_FALSE(
      InterpretAssertionExprAsBoolean(0, std::numeric_limits<uint64_t>::max()));
}

TEST(AssertionSampledArrayElement, SurvivesArrayMutationDuringEvaluationScope) {
  SampledArrayElement s = SampleArrayElementForAssertion(0xABCD);
  EXPECT_TRUE(SampledArrayElementStillReadable(s));

  SampledArrayElement after = ArrayElementAfterArrayMutation(s);
  EXPECT_TRUE(SampledArrayElementStillReadable(after));
  EXPECT_EQ(after.value, 0xABCDu);
}

TEST(AssertionSampledArrayElement,
     SurvivesRepeatedMutationsUntilEvaluationCompletes) {
  SampledArrayElement s = SampleArrayElementForAssertion(0x1234);
  for (int i = 0; i < 16; ++i) {
    s = ArrayElementAfterArrayMutation(s);
    EXPECT_TRUE(SampledArrayElementStillReadable(s));
    EXPECT_EQ(s.value, 0x1234u);
  }
}

TEST(AssertionBooleanExprPlace, SequenceOrPropertyExpressionsUseSampledValues) {
  EXPECT_TRUE(
      BooleanExprUsesSampledValues(BooleanExprPlace::kSequenceOrPropertyExpr));
}

TEST(AssertionBooleanExprPlace, ClockingEventIsExceptedFromSampledRule) {
  EXPECT_FALSE(BooleanExprUsesSampledValues(BooleanExprPlace::kClockingEvent));
}

TEST(AssertionBooleanExprPlace, DisableConditionUsesCurrentValuesNotSampled) {
  EXPECT_FALSE(
      BooleanExprUsesSampledValues(BooleanExprPlace::kDisableCondition));
  EXPECT_TRUE(DisableConditionUsesCurrentValues());
}

TEST(AssertionSampledArrayElement, QueueHeadSampledForTheTickOutlivesThePop) {
  SimFixture f;
  auto* held = RunAndFindVar(
      "module m;\n"
      "  logic clk = 0;\n"
      "  int q[$];\n"
      "  int held = 0;\n"
      "  assert property (@(posedge clk) q[0] == 5) held = held + 1;\n"
      "  initial begin\n"
      "    q.push_back(5);\n"
      "    #5 q.pop_front(); clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "held");
  ASSERT_NE(held, nullptr);
  EXPECT_EQ(held->value.ToUint64(), 1u);
}

TEST(ConcurrentBooleanTruthSim,
     MultiBitZRealAndUnknownValuesReadAsAnIfCondition) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module m;\n"
                "  logic clk = 0;\n"
                "  logic [3:0] v;\n"
                "  logic b;\n"
                "  real r;\n"
                "  int vp = 0, vf = 0, bp = 0, bf = 0, rp = 0, rf = 0;\n"
                "  logic [3:0] vs[7] = '{4'b0000, 4'b0100, 4'bxxxx, 4'bz000, "
                "4'b1x00, 4'b1z00, 4'bzzzz};\n"
                "  logic bs[7] = '{1'bz, 1'b1, 1'bz, 1'b0, 1'bz, 1'b1, 1'bz};\n"
                "  real rs[7] = '{0.0, 0.5, 0.0, 2.0, -1.5, 0.0, 0.0};\n"
                "  av: assert property (@(posedge clk) v) vp++; else vf++;\n"
                "  ab: assert property (@(posedge clk) b) bp++; else bf++;\n"
                "  ar: assert property (@(posedge clk) r) rp++; else rf++;\n"
                "  initial begin\n"
                "    for (int i = 0; i < 7; i++) begin\n"
                "      v = vs[i]; b = bs[i]; r = rs[i];\n"
                "      #5 clk = 1;\n"
                "      #5 clk = 0;\n"
                "    end\n"
                "    #5 $display(\"%0d %0d | %0d %0d | %0d %0d\", vp, vf, bp, "
                "bf, rp, rf);\n"
                "  end\n"
                "endmodule\n",
                f),
            "3 4 | 2 5 | 3 4\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConcurrentBooleanTruthSim, EveryPlaceOfABooleanReadsXAndZAsFalse) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "interface ifc(input logic clk, input logic [3:0] v);\n"
          "  int p = 0, f = 0;\n"
          "  ai: assert property (@(posedge clk) v) p++; else f++;\n"
          "endinterface\n"
          "checker chk(logic clk, logic [3:0] v);\n"
          "  int p = 0, f = 0;\n"
          "  ac: assert property (@(posedge clk) v) p++; else f++;\n"
          "endchecker\n"
          "program prg(input logic clk, input logic [3:0] v);\n"
          "  int p = 0, f = 0;\n"
          "  ap: assert property (@(posedge clk) v) p++; else f++;\n"
          "  initial #90 $display(\"prg %0d %0d\", p, f);\n"
          "endprogram\n"
          "module m;\n"
          "  logic clk = 0;\n"
          "  logic [3:0] v;\n"
          "  int sp = 0, sf = 0, cp = 0, qp = 0, qf = 0, np = 0, nf = 0, pp = "
          "0, pf = 0;\n"
          "  int ip = 0, if_ = 0, jp = 0, jf = 0, kp = 0, kf = 0, lp = 0, lf = "
          "0;\n"
          "  logic [3:0] vs[7] = '{4'b0000, 4'b0100, 4'bxxxx, 4'bz000, "
          "4'b1x00, 4'b1z00, 4'bzzzz};\n"
          "  sequence s; v; endsequence\n"
          "  property pr; v; endproperty\n"
          "  am: assume property (@(posedge clk) v) sp++; else sf++;\n"
          "  cv: cover property (@(posedge clk) v) cp++;\n"
          "  aq: assert property (@(posedge clk) 1 ##1 v) qp++; else qf++;\n"
          "  an: assert property (@(posedge clk) s) np++; else nf++;\n"
          "  ao: assert property (@(posedge clk) pr) pp++; else pf++;\n"
          "  ai: assert property (@(posedge clk) v |-> 0) ip++; else if_++;\n"
          "  aj: assert property (@(posedge clk) v |=> 0) jp++; else jf++;\n"
          "  ak: assert property (@(posedge clk) if (v) 1 else 0) kp++; else "
          "kf++;\n"
          "  always @(posedge clk) begin\n"
          "    al: assert property (v) lp++; else lf++;\n"
          "  end\n"
          "  ifc i(clk, v);\n"
          "  chk c(clk, v);\n"
          "  prg g(clk, v);\n"
          "  initial begin\n"
          "    for (int n = 0; n < 7; n++) begin\n"
          "      v = vs[n];\n"
          "      #5 clk = 1;\n"
          "      #5 clk = 0;\n"
          "    end\n"
          "    v = 0;\n"
          "    #5 clk = 1;\n"
          "    #5 clk = 0;\n"
          "    #5 $display(\"assume %0d %0d cover %0d seq %0d %0d named %0d "
          "%0d prop %0d %0d\", sp, sf, cp, qp, qf, np, nf, pp, pf);\n"
          "    $display(\"|-> %0d %0d |=> %0d %0d if %0d %0d proc %0d %0d\", "
          "ip, if_, jp, jf, kp, kf, lp, lf);\n"
          "    $display(\"ifc %0d %0d chk %0d %0d\", i.p, i.f, c.p, c.f);\n"
          "  end\n"
          "endmodule\n",
          f),
      "assume 3 5 cover 3 seq 3 4 named 3 5 prop 3 5\n|-> 5 3 |=> 5 3 if 3 5 "
      "proc 3 5\nifc 3 5 chk 3 5\nprg 3 5\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConcurrentBooleanTruthSim,
     ADisableConditionOfXOrZDoesNotDisableAndAKnownNonzeroDoes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module m;\n"
          "  logic clk = 0;\n"
          "  logic d1;\n"
          "  logic [3:0] d4;\n"
          "  int f1 = 0, f4 = 0;\n"
          "  logic ds[4] = '{1'bx, 1'bz, 1'b1, 1'b0};\n"
          "  logic [3:0] d4s[4] = '{4'b0100, 4'b0000, 4'b1x00, 4'bz0z0};\n"
          "  a1: assert property (@(posedge clk) disable iff (d1) 0) else "
          "f1++;\n"
          "  a4: assert property (@(posedge clk) disable iff (d4) 0) else "
          "f4++;\n"
          "  initial begin\n"
          "    for (int n = 0; n < 4; n++) begin\n"
          "      d1 = ds[n]; d4 = d4s[n];\n"
          "      #5 clk = 1;\n"
          "      #5 clk = 0;\n"
          "    end\n"
          "    #5 $display(\"%0d %0d\", f1, f4);\n"
          "  end\n"
          "endmodule\n",
          f),
      "3 2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConcurrentBooleanTruthSim, ADefaultDisableConditionOfXOrZDoesNotDisable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic clk = 0;\n"
                       "  logic d1;\n"
                       "  int f1 = 0;\n"
                       "  logic ds[4] = '{1'bx, 1'bz, 1'b1, 1'b0};\n"
                       "  default disable iff (d1);\n"
                       "  a1: assert property (@(posedge clk) 0) else f1++;\n"
                       "  initial begin\n"
                       "    for (int n = 0; n < 4; n++) begin\n"
                       "      d1 = ds[n];\n"
                       "      #5 clk = 1;\n"
                       "      #5 clk = 0;\n"
                       "    end\n"
                       "    #5 $display(\"%0d\", f1);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
