#include <gtest/gtest.h>

#include <string>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

const char kGlobal[] = "@($global_clock) ";
const char kPastConst[] = "$past(const'(a)) == const'(a)";

TEST(ConstCastSampling, ASampledConstCastIsTheCurrentValue) {
  ExpectEachAlwaysHolds({"$sampled(const'(a)) == const'(a)",
                         "$sampled(const'(a)) != a || const'(a) == a"});
}

TEST(ConstCastSampling, DISABLED_APastConstCastIsTheCurrentValue) {
  ExpectEachAlwaysHolds({kPastConst, "$past(const'(a), 2) == const'(a)"});
}

TEST(ConstCastSampling,
     DISABLED_AGatedOrReclockedPastConstCastIsTheCurrentValue) {
  ExpectEachAlwaysHolds({"$past(const'(a), 1, en) == const'(a)",
                         "$past(const'(a), 1, 1, @(posedge clk2)) == "
                         "const'(a)"});
}

TEST(ConstCastSampling, DISABLED_AConstCastNeverChangesBetweenTicks) {
  ExpectEachAlwaysHolds({"$stable(const'(a))", "!$changed(const'(a))",
                         "!$rose(const'(a))", "!$fell(const'(a))",
                         "!$rose(const'(v) > 4'd5)",
                         "!$fell(const'(v) > 4'd5)"});
}

TEST(ConstCastSampling,
     DISABLED_AGlobalClockPastOfAConstCastIsTheCurrentValue) {
  ExpectEachAlwaysHolds(
      {"$past_gclk(const'(v)) == const'(v)", "!$rose_gclk(const'(a))",
       "!$fell_gclk(const'(a))", "$stable_gclk(const'(v))",
       "!$changed_gclk(const'(v))"},
      kGlobal);
}

TEST(ConstCastSampling, AGlobalClockFutureOfAConstCastIsTheCurrentValue) {
  ExpectEachAlwaysHolds(
      {"$future_gclk(const'(v)) == const'(v)", "!$rising_gclk(const'(a))",
       "!$falling_gclk(const'(a))", "$steady_gclk(const'(v))",
       "!$changing_gclk(const'(v))"},
      kGlobal);
}

TEST(ConstCastSampling, DISABLED_AConstCastOfAnExpressionIsItsCurrentValue) {
  ExpectEachAlwaysHolds({"$past(const'(v + a)) == const'(v + a)"});
}

TEST(ConstCastSampling, DISABLED_OnlyTheConstCastInALargerArgumentIsCurrent) {
  ExpectEachAlwaysHolds({"$past(b & const'(a)) == ($past(b) & const'(a))"});
}

TEST(ConstCastSampling, AConstCastActualOfAPastFormalIsCurrent) {
  ExpectOnlyPasses(
      SampledBench("property pp(x); $past(x) == x; endproperty\n  " +
                   SampledVerdict("pp(const'(a))")));
}

TEST(ConstCastSampling, DISABLED_AProceduralPastOfAConstCastIsTheCurrentValue) {
  ExpectOnlyPasses(
      SampledBench("always @(posedge clk) " + ProceduralVerdict(kPastConst)));
}

TEST(ConstCastSampling,
     DISABLED_AProceduralAssertionsConstCastIsTheCurrentValue) {
  ExpectOnlyPasses(
      SampledBench("always @(posedge clk) " + SampledVerdict(kPastConst, "")));
}

TEST(ConstCastSampling, DISABLED_AGenerateBlocksConstCastIsTheCurrentValue) {
  ExpectOnlyPasses(
      SampledBench("if (1) begin : g " + SampledVerdict(kPastConst) + " end"));
}

std::string Unit(const char* open, const char* close, const char* instance,
                 const std::string& body) {
  return SampledBench(instance,
                      std::string(open) + "\n  " + body + "\n" + close + "\n");
}

struct Place {
  const char* open;
  const char* close;
  const char* instance;
  const char* procedure;
};

const Place kPlaces[] = {
    {"interface ifc(input logic clk, input logic a);", "endinterface",
     "ifc i(clk, a);", "always"},
    {"program p(input logic clk, input logic a);", "endprogram", "p u(clk, a);",
     "initial forever"},
    {"checker chk(logic clk, logic a);", "endchecker", "chk k(clk, a);",
     "always_ff"},
};

TEST(ConstCastSampling,
     DISABLED_AnInterfaceProgramOrCheckersConstCastIsCurrent) {
  for (const auto& p : kPlaces) {
    ExpectOnlyPasses(
        Unit(p.open, p.close, p.instance, SampledVerdict(kPastConst)));
  }
}

const char kLoop[] = "always @(posedge clk) for (int i = 0; i < 2; i++) ";

TEST(AutomaticSampling, DISABLED_APastLoopVariableInAnAssertionIsCurrent) {
  ExpectOnlyPasses(SampledBench(kLoop + SampledVerdict("$past(i) == i", "")));
}

TEST(AutomaticSampling, DISABLED_APastLoopVariableInProceduralCodeIsCurrent) {
  ExpectOnlyPasses(SampledBench(kLoop + ProceduralVerdict("$past(i) == i")));
}

TEST(AutomaticSampling, DISABLED_ADelayedOrGatedPastLoopVariableIsCurrent) {
  for (const char* expr : {"$past(i, 2) == i", "$past(i, 1, en) == i"}) {
    ExpectOnlyPasses(SampledBench(kLoop + SampledVerdict(expr, "")));
  }
}

const char kNoChange[] =
    "!$rose(k1) && !$fell(k1) && $stable(k1) && !$changed(k1) && "
    "!$rose(k4) && !$fell(k4) && $stable(k4) && !$changed(k4)";

std::string WithLocals(const std::string& body) {
  return "always @(posedge clk) begin automatic logic k1 = a; "
         "automatic logic [3:0] k4 = v; " +
         body + " end";
}

TEST(AutomaticSampling, DISABLED_AnAutomaticNeverChangesBetweenTicks) {
  ExpectOnlyPasses(SampledBench(WithLocals(SampledVerdict(kNoChange, ""))));
  ExpectOnlyPasses(SampledBench(WithLocals(ProceduralVerdict(kNoChange))));
}

TEST(AutomaticSampling, DISABLED_AGlobalClockPastOfAnAutomaticIsCurrent) {
  ExpectOnlyPasses(SampledBench(WithLocals(SampledVerdict(
      "$past_gclk(k4) == k4 && !$rose_gclk(k1) && !$fell_gclk(k1) && "
      "$stable_gclk(k4) && !$changed_gclk(k4)",
      kGlobal))));
}

TEST(AutomaticSampling, AGlobalClockFutureOfAnAutomaticIsCurrent) {
  ExpectOnlyPasses(SampledBench(WithLocals(SampledVerdict(
      "$future_gclk(k4) == k4 && !$rising_gclk(k1) && !$falling_gclk(k1) && "
      "$steady_gclk(k4) && !$changing_gclk(k4)",
      kGlobal))));
}

TEST(AutomaticSampling, DISABLED_ABlockLocalOfEveryProcedureKindIsCurrent) {
  const std::string kBody = "begin automatic logic [3:0] k = v; " +
                            SampledVerdict("$past(k) == k") + " end";
  for (const std::string& procedure :
       {"initial forever @(posedge clk) " + kBody,
        "always_ff @(posedge clk) " + kBody, "always_comb " + kBody}) {
    ExpectOnlyPasses(SampledBench(procedure));
  }
}

TEST(AutomaticSampling, DISABLED_ALoopVariableInAGenerateBlockIsCurrent) {
  ExpectOnlyPasses(SampledBench("if (1) begin : g " + std::string(kLoop) +
                                SampledVerdict("$past(i) == i", "") + " end"));
}

TEST(AutomaticSampling,
     DISABLED_ALoopVariableInAnInterfaceProgramOrCheckerIsCurrent) {
  for (const auto& p : kPlaces) {
    ExpectOnlyPasses(Unit(p.open, p.close, p.instance,
                          std::string(p.procedure) +
                              " @(posedge clk) for (int i = 0; i < 2; i++) " +
                              SampledVerdict("$past(i) == i")));
  }
}

TEST(AutomaticSampling, DISABLED_ACheckerFormalBoundToALoopVariableIsCurrent) {
  ExpectOnlyPasses(SampledBench(
      std::string(kLoop) + "begin cx k(i, clk); end",
      "checker cx(int x, logic c);\n  " +
          SampledVerdict("$past(x) == x", "@(posedge c) ") + "\nendchecker\n"));
}

TEST(AutomaticSampling, OnlyTheStaticPartOfAMixedArgumentIsPast) {
  ExpectOnlyPasses(SampledBench(
      "always @(posedge clk) for (int i = 0; i < 4; i++) " +
      SampledVerdict("$past(v[i]) == (($past(v) >> i) & 4'd1)", "")));
}

}  // namespace
