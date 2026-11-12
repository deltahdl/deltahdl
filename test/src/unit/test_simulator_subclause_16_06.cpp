#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <limits>
#include <string>

#include "fixture_simulator.h"
#include "helpers_sampling_bench.h"
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

const char kArrays[] =
    "  int q[$] = '{2, 5};\n"
    "  int d[] = '{2, 5};\n"
    "  int aa[int], sa[string], wa[*];\n";

std::string ArrayBench(const std::string& items, const std::string& change,
                       const std::string& outside = "") {
  return outside + "module top;\n  logic clk = 0;\n" + kArrays + "  " + items +
         "\n"
         "  initial begin\n"
         "    aa[7] = 5; sa[\"k\"] = 5; wa[7] = 5;\n"
         "    #5 " +
         change +
         " clk = 1;\n"
         "    #5 $finish;\n"
         "  end\n"
         "endmodule\n";
}

std::string Kept(const std::string& expr, const std::string& clock = "clk") {
  return "assert property (@(posedge " + clock + ") " + expr +
         ") $display(\"V%0t pass\", $time); else $display(\"V%0t fail\", "
         "$time);";
}

void ExpectEachChangeKeepsTheSample(
    const std::string& expr, std::initializer_list<const char*> changes) {
  for (const char* change : changes) {
    ExpectLines(ArrayBench(Kept(expr), change), "V", "5 pass");
  }
}

TEST(AssertionSampledArrayElement, AQueueElementOutlivesEveryRemoval) {
  ExpectEachChangeKeepsTheSample(
      "q[1] == 5", {"q.pop_back();", "q.delete(1);", "q.delete();", "q = {};",
                    "q = '{2};", "q.push_front(9);", "q.insert(0, 9);"});
}

TEST(AssertionSampledArrayElement, ADynamicArrayElementOutlivesEveryResize) {
  ExpectEachChangeKeepsTheSample(
      "d[1] == 5",
      {"d = new[1];", "d.delete();", "d = '{2};", "d = new[3]; d[1] = 9;"});
}

TEST(AssertionSampledArrayElement,
     DISABLED_AnAssociativeElementOutlivesItsDeletion) {
  ExpectEachChangeKeepsTheSample("aa[7] == 5", {"aa.delete(7);", "aa.delete();",
                                                "aa.delete(7); aa[7] = 6;"});
  ExpectEachChangeKeepsTheSample("sa[\"k\"] == 5", {"sa.delete(\"k\");"});
  ExpectEachChangeKeepsTheSample("wa[7] == 5", {"wa.delete(7);"});
}

TEST(AssertionSampledArrayElement, AnUnchangedAssociativeElementIsRead) {
  ExpectEachChangeKeepsTheSample("aa[7] == 5", {"aa.delete(8);"});
}

std::string LaterTickBench(const std::string& change) {
  return "module top;\n  logic clk = 0;\n" + std::string(kArrays) + "  " +
         Kept("1 ##1 aa[7] == 5") +
         "\n"
         "  initial begin\n"
         "    aa[7] = 5;\n"
         "    #5 clk = 1; #5 clk = 0;\n"
         "    #5 " +
         change +
         " clk = 1;\n"
         "    #5 $finish;\n"
         "  end\n"
         "endmodule\n";
}

TEST(AssertionSampledArrayElement,
     DISABLED_AnElementReadAtALaterTickOutlivesItsDeletion) {
  ExpectLines(LaterTickBench("aa.delete(7);"), "V", "15 pass");
}

TEST(AssertionSampledArrayElement, AnElementReadAtALaterTickIsReadUnchanged) {
  ExpectLines(LaterTickBench("aa.delete(8);"), "V", "15 pass");
}

std::string Assumed(const std::string& expr) {
  return "assume property (@(posedge clk) " + expr +
         ") $display(\"V%0t pass\", $time); else $display(\"V%0t fail\", "
         "$time);";
}

std::string Covered(const std::string& expr) {
  return "cover property (@(posedge clk) " + expr +
         ") $display(\"V%0t pass\", $time);";
}

std::string Procedural(const std::string& expr) {
  return "always @(posedge clk) assert property (" + expr +
         ") $display(\"V%0t pass\", $time); else $display(\"V%0t fail\", "
         "$time);";
}

std::string InGenerate(const std::string& expr) {
  return "if (1) begin : g " + Kept(expr) + " end";
}

void ExpectEachReaderKeepsTheSample(const std::string& expr,
                                    const std::string& change) {
  for (const std::string& items :
       {Assumed(expr), Covered(expr), Procedural(expr), InGenerate(expr)}) {
    ExpectLines(ArrayBench(items, change), "V", "5 pass");
  }
}

TEST(AssertionSampledArrayElement, EveryReaderKeepsAQueueElement) {
  ExpectEachReaderKeepsTheSample("q[1] == 5", "q.delete(1);");
}

TEST(AssertionSampledArrayElement, EveryReaderReadsAnUnchangedElement) {
  ExpectEachReaderKeepsTheSample("aa[7] == 5", "aa.delete(8);");
}

TEST(AssertionSampledArrayElement,
     DISABLED_EveryReaderKeepsAnAssociativeElement) {
  ExpectEachReaderKeepsTheSample("aa[7] == 5", "aa.delete(7);");
}

std::string Unit(const char* kind, const std::string& change) {
  return std::string(kind) +
         " u_unit;\n"
         "  logic uc = 0;\n"
         "  int ua[int];\n  " +
         Kept("ua[7] == 5", "uc") +
         "\n"
         "  initial begin ua[7] = 5; #5 ua." +
         change + " uc = 1; #5; end\nend" + kind + "\n";
}

void ExpectEachUnitKeepsTheSample(const std::string& change) {
  for (const char* kind : {"interface", "program"}) {
    ExpectLines(ArrayBench("u_unit u();", "", Unit(kind, change)), "V",
                "5 pass");
  }
}

const char kChecker[] =
    "checker ck(int arr[int], logic c);\n"
    "  assert property (@(posedge c) arr[7] == 5) $display(\"V%0t pass\", "
    "$time); else $display(\"V%0t fail\", $time);\n"
    "endchecker\n";

void ExpectTheCheckerKeepsTheSample(const std::string& change) {
  ExpectLines(ArrayBench("ck k(aa, clk);", "aa." + change, kChecker), "V",
              "5 pass");
}

TEST(AssertionSampledArrayElement, EveryUnitReadsAnUnchangedElement) {
  ExpectEachUnitKeepsTheSample("delete(8);");
}

TEST(AssertionSampledArrayElement,
     DISABLED_EveryUnitKeepsAnAssociativeElement) {
  ExpectEachUnitKeepsTheSample("delete(7);");
}

TEST(AssertionSampledArrayElement,
     DISABLED_ACheckerReadsAnUnchangedElementOfItsActual) {
  ExpectTheCheckerKeepsTheSample("delete(8);");
}

TEST(AssertionSampledArrayElement,
     DISABLED_ACheckerKeepsAnAssociativeElementOfItsActual) {
  ExpectTheCheckerKeepsTheSample("delete(7);");
}

const char kOneFailure[] = "5 pass 15 pass 25 pass 35 fail 45 pass";
const char kOneLaterFailure[] = "15 pass 25 pass 35 fail 45 pass";

std::string LiveBench(const std::string& items,
                      const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0, a = 1, live = 0, en = 1;\n"
         "  int tick = 0;\n"
         "  wire w;\n"
         "  assign w = live;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) begin\n"
         "    tick = tick + 1; live = (tick == 3); en = (tick != 3);\n"
         "  end\n"
         "  " +
         items +
         "\n"
         "  initial #48 $finish;\n"
         "endmodule\n";
}

std::string LiveVerdict(const std::string& head) {
  return head +
         " $display(\"V%0t pass\", $time); else $display(\"V%0t fail\", "
         "$time);";
}

void ExpectLive(const std::string& items, const char* expected,
                const std::string& outside = "") {
  ExpectLines(LiveBench(items, outside), "V", expected);
}

TEST(AssertionSampledOperand, AnIffGateReadsItsCurrentValue) {
  ExpectLive(LiveVerdict("assert property (@(posedge clk iff en) 1)"),
             "5 pass 15 pass 35 pass 45 pass");
}

TEST(AssertionSampledOperand, AnOperandAfterADelayReadsItsSampledValue) {
  ExpectLive(LiveVerdict("assert property (@(posedge clk) a ##1 !live)"),
             kOneLaterFailure);
}

TEST(AssertionSampledOperand, ANamedSequenceOrPropertyReadsSampledValues) {
  ExpectLive("sequence s; a ##1 !live; endsequence\n  " +
                 LiveVerdict("assert property (@(posedge clk) s)"),
             kOneLaterFailure);
  ExpectLive("property p; @(posedge clk) a ##1 !live; endproperty\n  " +
                 LiveVerdict("assert property (p)"),
             kOneLaterFailure);
}

TEST(AssertionSampledOperand, AnImplicationsConsequentReadsSampledValues) {
  ExpectLive(LiveVerdict("assert property (@(posedge clk) a |-> !live)"),
             kOneFailure);
  ExpectLive(LiveVerdict("assert property (@(posedge clk) a |=> !live)"),
             kOneLaterFailure);
}

TEST(AssertionSampledOperand, AnImplicationsAntecedentReadsSampledValues) {
  ExpectLive(LiveVerdict("assert property (@(posedge clk) live |-> 0)"),
             kOneFailure);
  ExpectLive(
      "assert property (@(posedge clk) live |=> 0) else "
      "$display(\"V%0t fail\", $time);",
      "45 fail");
}

TEST(AssertionSampledOperand, AnAssumptionReadsSampledValues) {
  ExpectLive(LiveVerdict("assume property (@(posedge clk) !live)"),
             kOneFailure);
}

TEST(AssertionSampledOperand, ACoverReadsSampledValues) {
  ExpectLive("cover property (@(posedge clk) live) $display(\"V%0t\", $time);",
             "35");
  ExpectLive("cover sequence (@(posedge clk) live) $display(\"V%0t\", $time);",
             "35");
}

TEST(AssertionSampledOperand, ANetReadsItsSampledValue) {
  ExpectLive(LiveVerdict("assert property (@(posedge clk) !w)"), kOneFailure);
}

std::string LiveUnit(const char* kind) {
  return std::string(kind) +
         " u_unit(input logic clk, input logic live);\n"
         "  " +
         LiveVerdict("assert property (@(posedge clk) !live)") + "\nend" +
         kind + "\n";
}

TEST(AssertionSampledOperand, AnInterfaceOrProgramReadsSampledValues) {
  for (const char* kind : {"interface", "program"}) {
    ExpectLive("u_unit u(clk, live);", kOneFailure, LiveUnit(kind));
  }
}

TEST(AssertionSampledOperand, AGenerateBlockReadsSampledValues) {
  ExpectLive("if (1) begin : g " +
                 LiveVerdict("assert property (@(posedge clk) !live)") + " end",
             kOneFailure);
  ExpectLive("for (genvar j = 0; j < 1; j++) begin : lg " +
                 LiveVerdict("assert property (@(posedge clk) !live)") + " end",
             kOneFailure);
}

const char kDisabledAtTheRise[] = "5 fail 15 fail 35 fail 45 fail";
const char kFailing[] = "assert property (@(posedge clk) !a)";

TEST(AssertionDisableCurrentValue, AFallingConditionLeavesTheAttemptEnabled) {
  ExpectLive(
      LiveVerdict("assert property (@(posedge clk) disable iff (en) !a)"),
      "25 fail");
}

TEST(AssertionDisableCurrentValue, ANamedPropertysConditionReadsCurrentValues) {
  ExpectLive(
      "property p; @(posedge clk) disable iff (live) !a; endproperty\n  " +
          LiveVerdict("assert property (p)"),
      kDisabledAtTheRise);
  ExpectLive(LiveVerdict("assert property (pq::pp(clk, live))"),
             kDisabledAtTheRise,
             "package pq;\n"
             "  property pp(logic c, logic x); @(posedge c) disable iff (x) 0; "
             "endproperty\n"
             "endpackage\n");
}

TEST(AssertionDisableCurrentValue, ADefaultConditionReadsCurrentValues) {
  ExpectLive("default disable iff (live);\n  " + LiveVerdict(kFailing),
             kDisabledAtTheRise);
}

std::string DefaultUnit(const char* kind) {
  const std::string kPorts = std::string(kind) == "checker"
                                 ? "(logic clk, logic live)"
                                 : "(input logic clk, input logic live)";
  return std::string(kind) + " u_unit" + kPorts +
         ";\n"
         "  default disable iff (live);\n  " +
         LiveVerdict("assert property (@(posedge clk) 0)") + "\nend" + kind +
         "\n";
}

TEST(AssertionDisableCurrentValue,
     EveryUnitsDefaultConditionReadsCurrentValues) {
  for (const char* kind : {"interface", "program", "checker"}) {
    ExpectLive("u_unit u(clk, live);", kDisabledAtTheRise, DefaultUnit(kind));
  }
  ExpectLive("if (1) begin : g\n    default disable iff (live);\n    " +
                 LiveVerdict(kFailing) + "\n  end",
             kDisabledAtTheRise);
}

TEST(AssertionDisableCurrentValue, AnInferredDisableFormalReadsCurrentValues) {
  ExpectLive("default disable iff (live);\n  ck k(clk);", kDisabledAtTheRise,
             "checker ck(logic clk, logic r = $inferred_disable);\n  " +
                 LiveVerdict("assert property (@(posedge clk) disable iff (r) "
                             "0)") +
                 "\nendchecker\n");
}

TEST(AssertionDisableCurrentValue, ATriggeredConditionDisablesAtTheEndPoint) {
  ExpectLive("sequence s; @(posedge clk) live; endsequence\n  " +
                 LiveVerdict("assert property (@(posedge clk) disable iff "
                             "(s.triggered) !a)"),
             "5 fail 15 fail 25 fail 45 fail");
}

TEST(AssertionDisableCurrentValue, ALaterTickOfAnAttemptReadsCurrentValues) {
  ExpectLive(LiveVerdict("assert property (@(posedge clk) disable iff (live) "
                         "a |=> 0)"),
             "15 fail 45 fail");
}

TEST(AssertionDisableCurrentValue, AProceduralAssertionReadsCurrentValues) {
  ExpectLive("always @(posedge clk) " +
                 LiveVerdict("assert property (disable iff (live) !a)"),
             kDisabledAtTheRise);
  ExpectLive("default disable iff (live);\n  always @(posedge clk) " +
                 LiveVerdict("assert property (!a)"),
             kDisabledAtTheRise);
}

TEST(AssertionDisableCurrentValue, AnAssumptionOrCoverReadsCurrentValues) {
  ExpectLive(
      LiveVerdict("assume property (@(posedge clk) disable iff (live) !a)"),
      kDisabledAtTheRise);
  ExpectLive(
      "cover property (@(posedge clk) disable iff (live) a) "
      "$display(\"V%0t\", $time);",
      "5 15 35 45");
}

TEST(AssertionDisableCurrentValue, AnExpectReadsCurrentValues) {
  ExpectLive("initial begin\n    #20 " +
                 LiveVerdict("expect (@(posedge clk) disable iff (en) 0)") +
                 "\n  end",
             "25 fail");
}

}  // namespace
