#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12: the result of property evaluation is either true or false. When
// an implication evaluation completes, EvalImplication returns one of the
// boolean outcomes (kPass / kFail) — never the not-yet-determined kPending.
TEST(PropertyEvaluation, PropertyEvaluationResultIsBoolean) {
  auto pass = EvalImplication(true, true, false);
  auto fail = EvalImplication(true, false, false);
  EXPECT_EQ(pass, PropertyResult::kPass);
  EXPECT_EQ(fail, PropertyResult::kFail);
  EXPECT_NE(pass, PropertyResult::kPending);
  EXPECT_NE(fail, PropertyResult::kPending);
}

// §16.12: a vacuous outcome still resolves to true; the rule is that an
// evaluation that completes yields a boolean.
TEST(PropertyEvaluation, VacuousResolvesToTrue) {
  auto v = EvalImplication(false, false, false);
  EXPECT_EQ(v, PropertyResult::kVacuousPass);
}

// §16.12: a disable iff that fires preempts evaluation; per the LRM this
// resolves as not-failed (modeled here as a vacuous pass), matching the
// "true or false" boundary at evaluation end.
TEST(PropertyEvaluation, DisableIffPreemptsToVacuousPass) {
  auto inner = EvalImplication(true, false, false);
  EXPECT_EQ(inner, PropertyResult::kFail);
  auto preempted = EvalWithDisableIff(true, inner);
  EXPECT_EQ(preempted, PropertyResult::kVacuousPass);
}

// --- Live cases: concurrent assertions over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; sig is high at ticks 2 and 3
// and rst at 2 and 4; and the assertion `items` declare count their passes
// and failures in `passes` and `fails`.
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

// §16.12: an attempt at which the disable condition is true is disabled,
// neither succeeding nor failing. `disable iff (rst) !sig` over the four
// ticks passes at 1, is disabled at 2 and 4, where rst is high, and fails at
// 3, where sig is high with rst low: one pass and one failure, where without
// the clause the failures at 2 and 3 make two of each.
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

// §16.12: the disable condition reads the variables' current values, not
// sampled ones. live is set by a blocking assignment at the edge of tick 3,
// so the attempt at 3 is disabled though live's sampled value there is 0,
// and a property reading !live, sampled, passes at 3 and fails at 4.
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

// §16.12: an instance of a named property with formal arguments is the
// property's body with the actuals substituted for the formals, its clock,
// disable condition and boolean alike; p_guarded(sig, rst) is the assertion
// above, one pass and one failure.
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

// §16.12: a named property may be instantiated before its declaration.
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

// §16.12 with §16.8: an instance of a property that omits a formal with a
// default actual takes the default. a is high at the rises of 5, 25 and 55 and
// b at 15, 35, 65 and 85, so `a ##1 b`, y defaulted to b, matches from 5, 25
// and 55, and `a ##3 b`, d defaulted to 3, from 5 and 55.
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

// §16.12 with §26.3: a property declared in a package is instantiated through
// a wildcard import by its bare name and by its package-qualified name, and
// means what the same property declared in the module means. a is high at
// the rises of 15 and 45 and b at 25 alone, so the attempt of 15 holds, that
// of 45 fails at 55, and the other eight hold vacuously, in all three forms.
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

// Asserts `pk::<inst>` on posedge clk from a module that does not import pk,
// whose declarations are `pkg`, with a high at the rises of 15 and 45 and b
// at 25 alone, and prints the passes and the failures.
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

// §16.12 with §26.3: the body of a package's property names the package's
// own sequence in the package's scope, so `s2(x, y)` is that sequence where
// the property is instantiated through the package scope from a module
// that imports nothing. The attempt of 15 holds, that of 45 fails at 55,
// and the other eight hold vacuously.
TEST(PropertyEvaluation, APackagePropertyInstantiatesItsPackagesSequence) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  sequence s2(x, y); x ##1 y; endsequence\n"
                "  property p2(x, y); x |-> s2(x, y); endproperty\n",
                "p2(a, b)"),
            "p=9 f=1\n");
}

// §16.12 with §26.3: so is a sequence of the package with no formals, named
// in the property's body without parentheses; `s1` holds at every attempt.
TEST(PropertyEvaluation, APackagePropertyNamesItsPackagesSequenceBare) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  sequence s1; 1; endsequence\n"
                "  property p1(x); x |-> s1; endproperty\n",
                "p1(a)"),
            "p=10 f=0\n");
}

// §16.8 with §26.3: a formal of a package's property named as one of the
// package's sequences is the formal inside the property's body, so `s2`
// there is the actual a.
TEST(PropertyEvaluation, APackagePropertysFormalHidesItsPackagesSequence) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  sequence s2(x, y); x ##1 y; endsequence\n"
                "  property p3(s2, y); s2 |=> y; endproperty\n",
                "p3(a, b)"),
            "p=9 f=1\n");
}

// §16.10 with §26.3: a local variable of a package's sequence named as one
// of the package's sequences is the local inside the sequence's body, so
// `s1` there holds the value assigned to it.
TEST(PropertyEvaluation, APackageSequencesLocalHidesItsPackagesSequence) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  sequence s1; 0; endsequence\n"
                "  sequence s3(x, y); bit s1; (x, s1 = 1) ##1 "
                "({s1, y} == 2'b11); endsequence\n"
                "  property p4(x, y); x |-> s3(x, y); endproperty\n",
                "p4(a, b)"),
            "p=9 f=1\n");
}

// §16.12 with §26.3: so is a local variable of a package's property, and
// the package's parameter it is assigned is the package's.
TEST(PropertyEvaluation, APackagePropertysLocalHidesItsPackagesSequence) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  localparam int K = 1;\n"
                "  sequence s1; 0; endsequence\n"
                "  property p5(x, y); bit s1; (x, s1 = K) |=> (s1 && y); "
                "endproperty\n",
                "p5(a, b)"),
            "p=9 f=1\n");
}

// §16.12 with §26.3: a function of the package that a property's body calls
// by its bare name is the package's.
TEST(PropertyEvaluation, APackagePropertyCallsItsPackagesFunction) {
  EXPECT_EQ(RunPackagePropertyWithoutImport(
                "  function automatic bit id(bit v); return v; endfunction\n"
                "  property p6(x, y); x |=> id(y); endproperty\n",
                "p6(a, b)"),
            "p=9 f=1\n");
}

}  // namespace
