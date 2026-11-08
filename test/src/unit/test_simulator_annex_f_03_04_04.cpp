#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(DerivedSampledValueFunctions, SampledIsTheExpression) {
  ExpectIdentity("$sampled(e[1])", "e[1]", 1);
}

TEST(DerivedSampledValueFunctions, RoseIsThePastLsbNotOneAndTheLsbOne) {
  ExpectIdentity("$rose(e)", "$past(e[0]) !== 1'b1 && e[0] === 1'b1", 2);
}

TEST(DerivedSampledValueFunctions, FellIsThePastLsbNotZeroAndTheLsbZero) {
  ExpectIdentity("$fell(e)", "$past(e[0]) !== 1'b0 && e[0] === 1'b0", 1);
}

TEST(DerivedSampledValueFunctions, StableIsThePastValueCaseEqualToTheValue) {
  ExpectIdentity("$stable(e)", "$past(e) === e", 2);
}

TEST(DerivedSampledValueFunctions, ChangedIsThePastValueCaseUnequalToTheValue) {
  ExpectIdentity("$changed(e)", "$past(e) !== e", 4);
}

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
