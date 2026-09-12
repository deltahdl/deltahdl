#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

// Annex F.5.3.1: neutral satisfaction.
//
// F.5.3.1 defines when a word neutrally satisfies each assertion statement:
// an always assert property statement at every enabled clock tick where its
// body passes or is disabled, an assume property statement exactly as the
// assert property statement with the same body, and a cover property
// statement where some enabled tick has the body pass. The model under
// elaborator/annex_f_neutral_satisfaction.h carries the equations; the cases
// here observe the three statements at a run, on the one body form the
// simulator evaluates, a clocked Boolean, where an assume or a cover property
// statement was parsed and discarded and so was judged on no word at all.

using namespace delta;

namespace {

// Three ticks with `a` sampled 0, 1 and 0, so the body passes at the second
// tick alone.
constexpr const char* kThreeTicks =
    "  initial begin\n"
    "    #10 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    a = 1;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    a = 0;\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "  end\n";

std::string Design(const std::string& statement) {
  return "module m;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  int hits = 0;\n"
         "  int misses = 0;\n" +
         statement + kThreeTicks + "endmodule\n";
}

// F.5.3.1: an always assume property statement is satisfied iff the assert
// property statement with the same body is, so its pass and fail actions run
// at the ticks the assert's would: one pass and two fails.
TEST(NeutralSatisfactionAtARun, AnAssumeIsJudgedAsTheAssertWithItsBody) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      Design("  assume property (@(posedge clk) a) hits = hits + 1;\n"
             "  else misses = misses + 1;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  auto* misses = f.ctx.FindVariable("misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(misses->value.ToUint64(), 2u);
}

// And an assume property statement with no action block reports a failing
// tick as an assert property statement does, §16.14.2 having a simulator
// check an assumption as it checks an assertion.
TEST(NeutralSatisfactionAtARun, AnAssumeWithoutActionsReportsAsAnAssert) {
  SimFixture f;
  auto* design =
      ElaborateSrc(Design("  assume property (@(posedge clk) a);\n"), f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

// F.5.3.1: an always cover property statement is satisfied where some enabled
// tick has the body pass, and §16.14.3 runs its pass statement once per such
// tick, so the one tick at which `a` was sampled 1 runs it once.
TEST(NeutralSatisfactionAtARun, ACoverPassesAtTheTicksItsBodyHolds) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      Design("  cover property (@(posedge clk) a) hits = hits + 1;\n"), f,
      "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
}

// A cover property statement has no failure: a tick at which the body does
// not hold is one the cover is not satisfied at, and nothing is reported.
TEST(NeutralSatisfactionAtARun, ACoverReportsNothingWhereItsBodyDoesNotHold) {
  SimFixture f;
  auto* design =
      ElaborateSrc(Design("  cover property (@(posedge clk) a);\n"), f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "");
}

// The cover reads the sampled word as the assert does: `a` rises in the time
// step of the tick, after the letter that tick sampled, so the body does not
// hold at that tick and the pass statement does not run.
TEST(NeutralSatisfactionAtARun, ACoverIsJudgedOnTheSampledWord) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module m;\n"
      "  logic clk = 0;\n"
      "  logic a = 0;\n"
      "  int hits = 0;\n"
      "  cover property (@(posedge clk) a) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 a = 1;\n"
      "    clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 0u);
}

}  // namespace
