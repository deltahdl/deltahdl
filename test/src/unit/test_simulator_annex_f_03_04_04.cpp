#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

// Annex F.3.4.4: derived sampled value functions.
//
// F.3.4.4 defines each sampled value function of §16.9.3 and §16.9.4 as an
// expression over the basic ones: $sampled(e) is e itself, $rose and $fell
// compare the LSB of e with its $past through case equality, $stable and
// $changed compare the whole of e with its $past, and the four _gclk forms
// that look back stand in the same relation to $past_gclk. Each case here
// runs the function and its defining expression in one property over a word
// where the function's answer changes from tick to tick, and counts the ticks
// the two agree at and the ticks the function answers 1 at, so a function
// answering a constant is caught by the second count and one answering the
// wrong thing by the first.

using namespace delta;

namespace {

// Six ticks with `e` sampled 00, 01, 0x, 01, 01 and 10, so the LSB rises at
// the second and the fourth tick, falls at the sixth, and the value is stable
// at the fifth tick and at the first, where $past answers the default sampled
// value 00 of §16.5.1. F.3.4.4 writes $past with its clock named; inside
// a property clocked on the same event the default arguments name it, which
// is why the expressions below write $past(b) for $past(b, 1, 1, c).
constexpr const char* kStimulus =
    "  initial begin\n"
    "    #5 clk = 1; #5 clk = 0;\n"
    "    e = 2'b01;\n"
    "    #5 clk = 1; #5 clk = 0;\n"
    "    e = 2'b0x;\n"
    "    #5 clk = 1; #5 clk = 0;\n"
    "    e = 2'b01;\n"
    "    #5 clk = 1; #5 clk = 0;\n"
    "    #5 clk = 1; #5 clk = 0;\n"
    "    e = 2'b10;\n"
    "    #5 clk = 1; #5 clk = 0;\n"
    "  end\n";

constexpr unsigned kTicks = 6;

// A module with a global clocking on the property's own clock, so a _gclk
// function samples where the property does, one property counting the ticks
// `function` and `definition` agree and disagree at, and one counting the
// ticks `function` answers 1 at.
std::string Design(const std::string& function, const std::string& definition) {
  return "module m;\n"
         "  logic clk = 0;\n"
         "  logic [1:0] e = 2'b00;\n"
         "  int agree = 0;\n"
         "  int disagree = 0;\n"
         "  int ones = 0;\n"
         "  global clocking gc @(posedge clk); endclocking\n"
         "  assert property (@(posedge clk) " +
         function + " === (" + definition +
         ")) agree = agree + 1;\n"
         "  else disagree = disagree + 1;\n"
         "  assert property (@(posedge clk) " +
         function + ") ones = ones + 1;\n" + kStimulus + "endmodule\n";
}

void ExpectIdentity(const std::string& function, const std::string& definition,
                    unsigned ones) {
  SimFixture f;
  auto* agree = RunAndFindVar(Design(function, definition), f, "agree");
  ASSERT_NE(agree, nullptr);
  EXPECT_EQ(agree->value.ToUint64(), kTicks);
  auto* disagree = f.ctx.FindVariable("disagree");
  ASSERT_NE(disagree, nullptr);
  EXPECT_EQ(disagree->value.ToUint64(), 0u);
  auto* hits = f.ctx.FindVariable("ones");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), ones);
}

// $sampled(e) is e: inside a property e is already its sampled value. The
// upper bit is the one read, which is 1 at the sixth tick alone and never x.
TEST(DerivedSampledValueFunctions, SampledIsTheExpression) {
  ExpectIdentity("$sampled(e[1])", "e[1]", 1);
}

// $rose(e, c) is $past(b, 1, 1, c) !== 1 && b === 1 for b the LSB of e: the
// LSB rises at the second tick from 0 and at the fourth from x.
TEST(DerivedSampledValueFunctions, RoseIsThePastLsbNotOneAndTheLsbOne) {
  ExpectIdentity("$rose(e)", "$past(e[0]) !== 1'b1 && e[0] === 1'b1", 2);
}

// $fell(e, c) is $past(b, 1, 1, c) !== 0 && b === 0: the LSB falls at the
// sixth tick alone, the x at the third being neither 0 nor 1.
TEST(DerivedSampledValueFunctions, FellIsThePastLsbNotZeroAndTheLsbZero) {
  ExpectIdentity("$fell(e)", "$past(e[0]) !== 1'b0 && e[0] === 1'b0", 1);
}

// $stable(e, c) is $past(e, 1, 1, c) === e, over the whole value.
TEST(DerivedSampledValueFunctions, StableIsThePastValueCaseEqualToTheValue) {
  ExpectIdentity("$stable(e)", "$past(e) === e", 2);
}

// $changed(e, c) is $past(e, 1, 1, c) !== e.
TEST(DerivedSampledValueFunctions, ChangedIsThePastValueCaseUnequalToTheValue) {
  ExpectIdentity("$changed(e)", "$past(e) !== e", 4);
}

// The four _gclk forms that look back are the same four over $past_gclk.
TEST(DerivedSampledValueFunctions, RoseGclkIsRoseOverPastGclk) {
  ExpectIdentity("$rose_gclk(e)", "$past_gclk(e[0]) !== 1'b1 && e[0] === 1'b1",
                 2);
}

TEST(DerivedSampledValueFunctions, FellGclkIsFellOverPastGclk) {
  ExpectIdentity("$fell_gclk(e)", "$past_gclk(e[0]) !== 1'b0 && e[0] === 1'b0",
                 1);
}

TEST(DerivedSampledValueFunctions, StableGclkIsStableOverPastGclk) {
  ExpectIdentity("$stable_gclk(e)", "$past_gclk(e) === e", 2);
}

TEST(DerivedSampledValueFunctions, ChangedGclkIsChangedOverPastGclk) {
  ExpectIdentity("$changed_gclk(e)", "$past_gclk(e) !== e", 4);
}

}  // namespace
