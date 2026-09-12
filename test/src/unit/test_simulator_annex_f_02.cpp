#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

// Annex F.2: overview.
//
// F.2 defines the semantics as a relation between a word, the sequence of the
// design's variables as sampled at each clock tick, and an assertion, and says
// what one instance of that relation stands for at a run: each evaluation of
// a concurrent assertion. A declarative assertion outside procedural code has
// an instance of the annex's equations for each starting clock event, and a
// procedural one, whose queueing F.2 leaves to §16.14.6, has each matured
// attempt described on its own. So at a run of three ticks each tick starts
// an evaluation and each evaluation has its own verdict, read off the letter
// its tick sampled.

using namespace delta;

namespace {

// A clock ticking at 10, 20 and 30, with `a` raised between the first two
// ticks and dropped between the last two, so the three letters sampled carry
// 0, 1 and 0 in that order. An evaluation per tick counts one pass and two
// fails; an implementation evaluating once at the first tick counts one fail
// and nothing more, and one evaluating only the last state the same.
constexpr const char* kStimulus =
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

std::string WithAssertion(const std::string& assertion) {
  return "module m;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  int hits = 0;\n"
         "  int misses = 0;\n" +
         assertion + kStimulus + "endmodule\n";
}

// F.2: a declarative assertion has an instance of the equations for each
// starting clock event, so the three ticks are three evaluations with three
// verdicts of their own.
TEST(FormalSemanticsOverview,
     ADeclarativeAssertionIsEvaluatedOncePerStartingClockEvent) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      WithAssertion("  assert property (@(posedge clk) a) hits = hits + 1;\n"
                    "  else misses = misses + 1;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  auto* misses = f.ctx.FindVariable("misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(misses->value.ToUint64(), 2u);
}

// F.2: the annex leaves the queueing of a procedural concurrent assertion's
// instances to §16.14.6 and takes each matured attempt on its own, so the
// attempt the procedure queues at each tick is judged on that tick's letter
// and the three verdicts are the declarative assertion's.
TEST(FormalSemanticsOverview, EachMaturedProceduralAttemptIsJudgedOnItsOwn) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      WithAssertion("  always @(posedge clk) assert property (a) hits = hits "
                    "+ 1; else misses = misses + 1;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  auto* misses = f.ctx.FindVariable("misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(misses->value.ToUint64(), 2u);
}

}  // namespace
