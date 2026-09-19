#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

struct SvaFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

namespace {

// §16.12.9: for the overlapped followed-by (#-#) the consequent property_expr
// is evaluated at the end point of the antecedent match, so a matched
// antecedent yields exactly the consequent's verdict.
TEST(SvaEngine, OverlappingFollowedBy) {
  EXPECT_EQ(EvalFollowedBy(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalFollowedBy(true, false, false), PropertyResult::kFail);
}

// §16.12.9: the followed-by requires the antecedent sequence_expr to have at
// least one successful match. With no match the result is a definite fail — the
// dual of implication's vacuous pass — independent of the consequent and of the
// overlap flag, since EvalFollowedBy negates the vacuously-holding dual
// implication before the consequent is ever consulted.
TEST(SvaEngine, FollowedByRequiresAntecedentMatch) {
  EXPECT_EQ(EvalFollowedBy(false, true, false), PropertyResult::kFail);
  EXPECT_EQ(EvalFollowedBy(false, false, false), PropertyResult::kFail);
  EXPECT_EQ(EvalFollowedBy(false, true, true), PropertyResult::kFail);
  EXPECT_EQ(EvalFollowedBy(false, false, true), PropertyResult::kFail);
}

// §16.12.9: for the nonoverlapped followed-by (#=#) the consequent starts one
// clock tick after the antecedent match, so a matched antecedent defers its
// verdict rather than resolving immediately.
TEST(SvaEngine, NonOverlappingFollowedByDefers) {
  EXPECT_EQ(EvalFollowedBy(true, true, true), PropertyResult::kPending);
  EXPECT_EQ(EvalFollowedBy(true, false, true), PropertyResult::kPending);
}

// §16.12.9: the nonoverlapped followed-by (#=#) defers only for a nonempty
// antecedent match. When the antecedent attains an empty match the consequent
// starts at the nearest clock tick from where the sequence begins — the current
// tick for a singly clocked property — so the verdict settles immediately
// rather than staying pending, yielding the consequent's verdict directly.
TEST(SvaEngine, NonOverlappingFollowedByEmptyMatchSettlesImmediately) {
  EXPECT_EQ(EvalFollowedBy(true, true, true, /*antecedent_empty_match=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalFollowedBy(true, false, true, /*antecedent_empty_match=*/true),
            PropertyResult::kFail);
  // Contrast: with a nonempty match the same #=# verdict is still deferred.
  EXPECT_EQ(EvalFollowedBy(true, true, true, /*antecedent_empty_match=*/false),
            PropertyResult::kPending);
}

// §16.12.9: a deferred nonoverlapped followed-by is settled at the next tick;
// when the consequent then holds, the overall followed-by passes.
TEST(SvaEngine, NonOverlappingFollowedByResolvesPass) {
  EXPECT_EQ(EvalFollowedBy(true, false, true), PropertyResult::kPending);
  EXPECT_EQ(ResolveFollowedByNonOverlapping(true), PropertyResult::kPass);
}

// §16.12.9: when the consequent fails at the settling tick, the overall
// followed-by fails.
TEST(SvaEngine, NonOverlappingFollowedByResolvesFail) {
  EXPECT_EQ(EvalFollowedBy(true, false, true), PropertyResult::kPending);
  EXPECT_EQ(ResolveFollowedByNonOverlapping(false), PropertyResult::kFail);
}

// §16.12.9: the followed-by operators are the duals of the implication
// operators — `s #-# p` ≡ not (s |-> not p). Comparing the overlapped
// followed-by against that dual, hand-built from the §16.12.7 primitives,
// confirms the production code honors the stated equivalence over every
// antecedent/consequent combination rather than, say, holding vacuously.
TEST(SvaEngine, OverlappingFollowedByMatchesImplicationDual) {
  for (bool a : {false, true}) {
    for (bool c : {false, true}) {
      PropertyResult dual = EvalPropertyNot(EvalImplication(a, !c, false));
      EXPECT_EQ(EvalFollowedBy(a, c, false), dual);
    }
  }
}

// §16.12.9: the nonoverlapped followed-by is the dual of nonoverlapped
// implication — `s #=# p` ≡ not (s |=> not p). The dual is built from the
// §16.12.7 primitives with the same deferral handling the production path uses:
// a matched antecedent leaves the verdict pending (to be settled a tick later),
// while a missing match negates the vacuous hold to a definite fail. Comparing
// EvalFollowedBy against that dual over every antecedent/consequent combination
// confirms the production code honors the equivalence for the #=# operator too.
TEST(SvaEngine, NonOverlappingFollowedByMatchesImplicationDual) {
  for (bool a : {false, true}) {
    for (bool c : {false, true}) {
      PropertyResult implied = EvalImplication(a, !c, true);
      PropertyResult dual = (implied == PropertyResult::kPending)
                                ? PropertyResult::kPending
                                : EvalPropertyNot(implied);
      EXPECT_EQ(EvalFollowedBy(a, c, true), dual);
    }
  }
}

// --- Live cases: followed-by properties over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; req is high at ticks 1, 2 and
// 4, gnt at 1 and 4, done at 3 and rst at 2. `items` declare the
// assertions, counting in `passes` and `fails`.
std::string FollowedBySource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic req, gnt, done, rst;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign req = tick inside {1, 2, 4};\n"
         "  assign gnt = tick inside {1, 4};\n"
         "  assign done = tick inside {3};\n"
         "  assign rst = tick inside {2};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

// §16.12.9: `req #-# gnt` is true if and only if req matches at the
// attempt's tick and gnt holds at that end point, so unlike `req |-> gnt` it
// is false where req has no match: true at 1 and 4, false at 2 and 3.
TEST(FollowedByProperty, OverlappedNeedsAMatchWithTheConsequentTrue) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      FollowedBySource("  p: assert property (@(posedge clk) req #-# gnt) "
                       "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

// §16.12.9: `req #=# gnt` reads gnt the tick after the match: the attempts
// from 1 and 2 fail at 2 and 3, the attempt from 3 has no match and fails,
// and the attempt from 4, its consequent beginning at a tick the run never
// reaches, fails when the run ends.
TEST(FollowedByProperty, NonoverlappedReadsTheConsequentTheTickAfter) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      FollowedBySource("  p: assert property (@(posedge clk) req #=# gnt) "
                       "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 4u);
}

// §16.12.9: the clause's p1 with `!rst` as the consequent, `##[0:5] done
// #-# !rst`, is true where done holds at some tick of the window with rst
// low there: the attempts from 1, 2 and 3 are true at 3, and the attempt
// from 4, its window unfinished when the run ends with no match, fails
// then.
TEST(FollowedByProperty, WindowedAntecedentIsTrueAtTheMatchWithTheConsequent) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      FollowedBySource("  p: assert property (@(posedge clk) ##[0:5] done #-# "
                       "!rst) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.9: `s #-# p` is `not (s |-> not p)`, so the two read alike: `not
// (req |-> not gnt)` counts as `req #-# gnt` does.
TEST(FollowedByProperty, IsTheDualOfTheImplication) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      FollowedBySource("  p: assert property (@(posedge clk) not (req |-> not "
                       "gnt)) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

}  // namespace
