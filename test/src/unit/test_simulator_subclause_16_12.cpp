#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PropertyEvaluation, PropertyEvaluationResultIsBoolean) {
  auto pass = EvalImplication(true, true, false);
  auto fail = EvalImplication(true, false, false);
  EXPECT_EQ(pass, PropertyResult::kPass);
  EXPECT_EQ(fail, PropertyResult::kFail);
  EXPECT_NE(pass, PropertyResult::kPending);
  EXPECT_NE(fail, PropertyResult::kPending);
}

TEST(PropertyEvaluation, VacuousResolvesToTrue) {
  auto v = EvalImplication(false, false, false);
  EXPECT_EQ(v, PropertyResult::kVacuousPass);
}

TEST(PropertyEvaluation, DisableIffPreemptsToVacuousPass) {
  auto inner = EvalImplication(true, false, false);
  EXPECT_EQ(inner, PropertyResult::kFail);
  auto preempted = EvalWithDisableIff(true, inner);
  EXPECT_EQ(preempted, PropertyResult::kVacuousPass);
}

std::string PropertySource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic sig, rst;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign sig = tick inside {2, 3};\n"
         "  assign rst = tick inside {2, 4};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

const char* const kCounting = " passes++; else fails++;\n";

TEST(DeclaringProperties, DisableIffDisablesTheAttempt) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      PropertySource(std::string("  a: assert property (@(posedge clk) "
                                 "disable iff (rst) !sig)") +
                     kCounting),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  SimFixture g;
  auto* plain = RunAndFindVar(
      PropertySource(std::string("  a: assert property (@(posedge clk) !sig)") +
                     kCounting),
      g, "passes");
  ASSERT_NE(plain, nullptr);
  EXPECT_EQ(plain->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(DeclaringProperties, DisableConditionReadsTheCurrentValue) {
  const std::string kLive =
      "  logic live = 0;\n"
      "  always @(posedge clk) live = (tick == 3);\n";
  SimFixture f;
  auto* passes = RunAndFindVar(
      PropertySource(kLive +
                     "  a: assert property (@(posedge clk) disable iff (live) "
                     "!sig)" +
                     kCounting),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  SimFixture g;
  auto* sampled = RunAndFindVar(
      PropertySource(kLive + "  a: assert property (@(posedge clk) !live)" +
                     kCounting),
      g, "passes");
  ASSERT_NE(sampled, nullptr);
  EXPECT_EQ(sampled->value.ToUint64(), 3u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(DeclaringProperties, InstanceActualsAreBoundToTheFormals) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      PropertySource(std::string("  property p_guarded(x, r);\n"
                                 "    @(posedge clk) disable iff (r) !x;\n"
                                 "  endproperty\n"
                                 "  a: assert property (p_guarded(sig, rst))") +
                     kCounting),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

TEST(DeclaringProperties, InstanceMayPrecedeTheDeclaration) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      PropertySource(std::string("  a: assert property (p_low(sig))") +
                     kCounting +
                     "  property p_low(x);\n"
                     "    @(posedge clk) !x;\n"
                     "  endproperty\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(DeclaringProperties, ASpecWithoutItsSemicolonIsEvaluated) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      PropertySource(
          std::string("  int next_fails = 0;\n"
                      "  property p_guarded(x, r);\n"
                      "    @(posedge clk) disable iff (r) !x\n"
                      "  endproperty\n"
                      "  property p_next(x);\n"
                      "    @(posedge clk) x |=> !x\n"
                      "  endproperty\n"
                      "  n: assert property (p_next(sig)) else next_fails++;\n"
                      "  a: assert property (p_guarded(sig, rst))") +
          kCounting),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("next_fails")->value.ToUint64(), 1u);
}

TEST(PropertyEvaluation, AnOmittedPropertyFormalTakesItsDefault) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1010010000, bv = 10'b0101001010;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  int c1 = 0, c2 = 0;\n"
      "  property p_def(x, y = b); x ##1 y; endproperty\n"
      "  property p_del(x, int d = 3); x ##d b; endproperty\n"
      "  cover property (@(posedge clk) p_def(a)) c1++;\n"
      "  cover property (@(posedge clk) p_del(a)) c2++;\n"
      "  initial #98 $display(\"c1=%0d c2=%0d\", c1, c2);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=3 c2=2\n"), std::string::npos);
}

TEST(PropertyEvaluation, APackagePropertyIsInstantiatedByImportAndByScope) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  property p2(x, y); x |=> y; endproperty\n"
      "endpackage\n"
      "module t;\n"
      "  import pk::*;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b0100100000, bv = 10'b0010000000;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  int p = 0, f = 0, p2 = 0, f2 = 0, p3 = 0, f3 = 0;\n"
      "  property pl(x, y); x |=> y; endproperty\n"
      "  assert property (@(posedge clk) pl(a, b)) p++; else f++;\n"
      "  assert property (@(posedge clk) p2(a, b)) p2++; else f2++;\n"
      "  assert property (@(posedge clk) pk::p2(a, b)) p3++; else f3++;\n"
      "  initial #98 $display(\"%0d %0d %0d %0d %0d %0d\", p, f, p2, f2, p3, "
      "f3);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9 1 9 1 9 1\n");
}

TEST(PropertyEvaluation, ABareInstanceOfAnImportedPropertyIsTheAssertion) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk; property p(c, x); @(posedge c) x; endproperty\n"
      "endpackage\n"
      "module t; import pk::*;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b0100100000; bit a; assign a = av[0];\n"
      "  always @(negedge clk) av <= av << 1;\n"
      "  int p = 0, f = 0;\n"
      "  a1: assert property (p(clk, a)) p++; else f++;\n"
      "  initial #98 $display(\"p=%0d f=%0d\", p, f);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "p=2 f=8\n");
}

std::string RunPackagePropertyWithoutImport(const std::string& pkg,
                                            const std::string& inst) {
  SimFixture f;
  return RunCapture(
      "package pk;\n" + pkg +
          "endpackage\n"
          "module t;\n"
          "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
          "  bit [0:9] av = 10'b0100100000, bv = 10'b0010000000;\n"
          "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
          "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
          "  int p = 0, f = 0;\n"
          "  assert property (@(posedge clk) pk::" +
          inst +
          ") p++; else f++;\n"
          "  initial #98 $display(\"p=%0d f=%0d\", p, f);\n"
          "endmodule\n",
      f);
}

TEST(PropertyEvaluation, APackagePropertyInstantiatesItsPackagesSequence) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  sequence s2(x, y); x ##1 y; endsequence\n"
                "  property p2(x, y); x |-> s2(x, y); endproperty\n",
                "p2(a, b)"),
            "p=9 f=1\n");
}

TEST(PropertyEvaluation, APackagePropertyNamesItsPackagesSequenceBare) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  sequence s1; 1; endsequence\n"
                "  property p1(x); x |-> s1; endproperty\n",
                "p1(a)"),
            "p=10 f=0\n");
}

TEST(PropertyEvaluation, APackagePropertysFormalHidesItsPackagesSequence) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  sequence s2(x, y); x ##1 y; endsequence\n"
                "  property p3(s2, y); s2 |=> y; endproperty\n",
                "p3(a, b)"),
            "p=9 f=1\n");
}

TEST(PropertyEvaluation, APackageSequencesLocalHidesItsPackagesSequence) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  sequence s1; 0; endsequence\n"
                "  sequence s3(x, y); bit s1; (x, s1 = 1) ##1 "
                "({s1, y} == 2'b11); endsequence\n"
                "  property p4(x, y); x |-> s3(x, y); endproperty\n",
                "p4(a, b)"),
            "p=9 f=1\n");
}

TEST(PropertyEvaluation, APackagePropertysLocalHidesItsPackagesSequence) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  localparam int K = 1;\n"
                "  sequence s1; 0; endsequence\n"
                "  property p5(x, y); bit s1; (x, s1 = K) |=> (s1 && y); "
                "endproperty\n",
                "p5(a, b)"),
            "p=9 f=1\n");
}

TEST(PropertyEvaluation, APackagePropertyCallsItsPackagesFunction) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  function automatic bit id(bit v); return v; endfunction\n"
                "  property p6(x, y); x |=> id(y); endproperty\n",
                "p6(a, b)"),
            "p=9 f=1\n");
}

std::string RunPropertyFormalCase(const std::string& decl,
                                  const std::string& asserts) {
  SimFixture f;
  return RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1010101010, bv = 10'b0101010101;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  wire a = av[0], b = bv[0];\n"
      "  int p1 = 0, f1 = 0, p2 = 0, f2 = 0;\n" +
          decl + asserts +
          "  initial #98 $display(\"%0d %0d %0d %0d\", p1, f1, p2, f2);\n"
          "endmodule\n",
      f);
}

TEST(DeclaringProperties, AFormalStandsForAPropertySpec) {
  EXPECT_EQ(RunPropertyFormalCase(
                "  property p_spec(q); q; endproperty\n",
                "  assert property (p_spec(@(posedge clk) a |=> b)) p1++;\n"
                "    else f1++;\n"
                "  assert property (p_spec(@(posedge clk) a |=> a)) p2++;\n"
                "    else f2++;\n"),
            "10 0 5 5\n");
}

TEST(DeclaringProperties, AFormalStandsForAPropertyExpr) {
  EXPECT_EQ(RunPropertyFormalCase(
                "  property p_expr(q); a |-> q; endproperty\n",
                "  assert property (@(posedge clk) p_expr(##1 b)) p1++;\n"
                "    else f1++;\n"
                "  assert property (@(posedge clk) p_expr(##1 a)) p2++;\n"
                "    else f2++;\n"),
            "10 0 5 5\n");
}

constexpr const char* kPulseInFlight =
    "  assign a = tick inside {1};\n"
    "  assign b = tick inside {4};\n"
    "  assign c = 0;\n"
    "  initial begin d = 0; #20 d = 1; #2 d = 0; end\n";

const PlacedProperty kDisabledInFlight[] = {
    {"disable iff (d) a |=> ##2 b", {3, 0}, 3},
    {"disable iff (d) a |=> ##2 c", {3, 0}, 3},
    {"disable iff (d) a ##3 b", {0, 3}, 0}};

TEST(DisableConditionRun,
     DISABLED_APulseBetweenTicksDisablesTheAttemptInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kDisabledInFlight) {
      ExpectPropertyCountsInPlace(place, property, kPulseInFlight);
    }
  }
}

const PlacedProperty kNotDisabledInFlight[] = {
    {"a |=> ##2 b", {4, 0}, 4},
    {"a |=> ##2 c", {3, 1}, 3},
    {"disable iff (1'b0) a |=> ##2 c", {3, 1}, 3},
    {"a ##3 b", {1, 3}, 1},
    {"disable iff (1'b0) a ##3 b", {1, 3}, 1}};

TEST(DisableConditionRun, AFormNotDisabledCountsOnThePulseWaveformInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kNotDisabledInFlight) {
      ExpectPropertyCountsInPlace(place, property, kPulseInFlight);
    }
  }
}

constexpr const char* kTwoAttempts =
    "  assign a = tick inside {1, 3};\n"
    "  assign c = 0;\n";

TEST(DisableConditionRun,
     DISABLED_APulseDisablesOnlyTheAttemptInFlightInEachPlace) {
  const std::string kStimulus =
      std::string(kTwoAttempts) +
      "  initial begin d = 0; #27 d = 1; #2 d = 0; end\n";
  for (const char* place : kPropertyPlaces) {
    ExpectPropertyCountsInPlace(place, {"disable iff (d) a |=> c", {2, 1}, 2},
                                kStimulus);
  }
}

TEST(DisableConditionRun, APulseBeforeAnAttemptStartsLeavesItAloneInEachPlace) {
  const std::string kStimulus =
      std::string(kTwoAttempts) +
      "  initial begin d = 0; #20 d = 1; #2 d = 0; end\n";
  for (const char* place : kPropertyPlaces) {
    ExpectPropertyCountsInPlace(place, {"disable iff (d) a |=> c", {2, 2}, 2},
                                kStimulus);
  }
}

constexpr const char* kDefaultDisablePlaces[] = {"module",   "procedural",
                                                 "generate", "interface",
                                                 "program",  "module property"};

TEST(
    DisableConditionRun,
    DISABLED_ADefaultDisableIffPulseBetweenTicksDisablesTheAttemptInEachPlace) {
  for (const char* place : kDefaultDisablePlaces) {
    ExpectPropertyCountsInPlace(place, {"a |=> ##2 c", {3, 0}, 3},
                                kPulseInFlight, "  default disable iff d;\n");
  }
}

size_t CoverSequenceHits(const std::string& seq) {
  return CountThroughTheEnd(
             PlacedTop(kPulseInFlight, "  cover sequence (@(posedge clk) " +
                                           seq + ") $display(\"PASS\");\n"))
      .passes;
}

TEST(DisableConditionRun, ACoverSequenceWithoutADisableConditionMatches) {
  EXPECT_EQ(CoverSequenceHits("a ##3 b"), 1u);
  EXPECT_EQ(CoverSequenceHits("disable iff (1'b0) a ##3 b"), 1u);
}

TEST(DisableConditionRun,
     DISABLED_APulseBetweenTicksDisablesACoverSequenceAttempt) {
  EXPECT_EQ(CoverSequenceHits("disable iff (d) a ##3 b"), 0u);
}

TEST(DisableConditionRun,
     DISABLED_APulseBetweenTicksDisablesTheAttemptInACompilationUnitProperty) {
  for (const PlacedProperty& property : kDisabledInFlight) {
    ExpectPropertyCountsInPlace("unit", property, kPulseInFlight);
  }
}

}  // namespace
