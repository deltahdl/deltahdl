#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

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

// §16.12.7: for the overlapped form (|->) the consequent is evaluated at the
// end point of the antecedent match, so a matched antecedent yields exactly the
// consequent's verdict. With no antecedent match the implication holds
// vacuously.
TEST(SvaEngine, OverlappingImplication) {
  EXPECT_EQ(EvalImplication(true, true, false), PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, false), PropertyResult::kFail);

  EXPECT_EQ(EvalImplication(false, false, false), PropertyResult::kVacuousPass);
}

// §16.12.7: for the nonoverlapped form (|=>) the consequent starts one clock
// tick after the antecedent match, so a matched antecedent defers its verdict
// rather than resolving immediately. With no antecedent match the implication
// still holds vacuously.
TEST(SvaEngine, NonOverlappingImplication) {
  EXPECT_EQ(EvalImplication(true, true, true), PropertyResult::kPending);
  EXPECT_EQ(EvalImplication(false, false, true), PropertyResult::kVacuousPass);
}

// §16.12.7: a deferred nonoverlapped implication is settled at the next tick;
// when the consequent then holds, the overall implication passes.
TEST(SvaEngine, PropertyPendingResolvesPass) {
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  auto resolved = ResolveNonOverlapping(true);
  EXPECT_EQ(resolved, PropertyResult::kPass);
}

// §16.12.7: a deferred nonoverlapped implication is settled at the next tick;
// when the consequent fails there, the overall implication fails.
TEST(SvaEngine, PropertyPendingResolvesFail) {
  auto r1 = EvalImplication(true, false, true);
  EXPECT_EQ(r1, PropertyResult::kPending);

  auto resolved = ResolveNonOverlapping(false);
  EXPECT_EQ(resolved, PropertyResult::kFail);
}

// §16.12.7: the nonoverlapped form (|=>) defers its verdict only when the
// antecedent match is nonempty. When the antecedent matches empty, the
// consequent starts at the nearest clock tick from where the sequence begins,
// which for a singly clocked property is the current clock tick — so the
// verdict settles immediately from the consequent, with no kPending deferral,
// exactly like the overlapped form. This distinguishes the empty-match input of
// the nonoverlapped rule from the nonempty-match input that still defers.
TEST(SvaEngine, NonOverlappingEmptyAntecedentMatchResolvesImmediately) {
  EXPECT_EQ(EvalImplication(true, true, /*non_overlapping=*/true,
                            /*antecedent_empty_match=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalImplication(true, false, /*non_overlapping=*/true,
                            /*antecedent_empty_match=*/true),
            PropertyResult::kFail);
  // Contrast: the same nonoverlapped operands with a nonempty match still
  // defer.
  EXPECT_EQ(EvalImplication(true, true, /*non_overlapping=*/true,
                            /*antecedent_empty_match=*/false),
            PropertyResult::kPending);
}

// §16.12.7: from a given start point the antecedent may match zero, one, or
// more than once, and the consequent is evaluated separately at each match's
// end point. The implication from that start point holds only if the consequent
// holds at every match — a single failing match fails the whole attempt — while
// no antecedent match at all holds vacuously. This observes the multi-match
// aggregation, an input form the single-match EvalImplication cannot express.
TEST(SvaEngine, ImplicationHoldsOnlyIfEveryAntecedentMatchConsequentHolds) {
  // Zero matches from the start point: the implication holds vacuously.
  EXPECT_EQ(EvalImplicationOverMatches({}), PropertyResult::kVacuousPass);

  // Exactly one match whose consequent holds.
  EXPECT_EQ(EvalImplicationOverMatches({PropertyResult::kPass}),
            PropertyResult::kPass);

  // More than one match, every consequent holds (a vacuous consequent counts as
  // holding) → the whole attempt passes.
  EXPECT_EQ(EvalImplicationOverMatches({PropertyResult::kPass,
                                        PropertyResult::kVacuousPass,
                                        PropertyResult::kPass}),
            PropertyResult::kPass);

  // More than one match, one consequent fails → the whole attempt fails, even
  // though the other matches' consequents held.
  EXPECT_EQ(
      EvalImplicationOverMatches({PropertyResult::kPass, PropertyResult::kFail,
                                  PropertyResult::kPass}),
      PropertyResult::kFail);
}

// §16.12.7 edge case: with no antecedent match the implication holds vacuously,
// and that verdict is independent of the consequent — a consequent that would
// itself hold does not promote the vacuous hold to an ordinary pass, in either
// the overlapped or the nonoverlapped form. This exercises the antecedent
// short-circuit in EvalImplication, which returns before the consequent or the
// overlap flag are consulted.
TEST(SvaEngine, NoAntecedentMatchHoldsVacuouslyRegardlessOfConsequent) {
  EXPECT_EQ(EvalImplication(false, true, false), PropertyResult::kVacuousPass);
  EXPECT_EQ(EvalImplication(false, true, true), PropertyResult::kVacuousPass);
}

// --- Live cases: implications over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; req is high at ticks 1, 2 and
// 4, gnt at 1 and 4, ack at 2 and 3, done at 2 and 3 and late at 2, so req
// ##[1:2] ack matches from 1 at 2 and at 3, from 2 at 3, not at all from 3,
// and is unfinished from 4 when the run ends. `items` declare the
// assertions, counting in `passes` and `fails`.
std::string ImplicationSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic req, gnt, ack, done, late;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign req = tick inside {1, 2, 4};\n"
         "  assign gnt = tick inside {1, 4};\n"
         "  assign ack = tick inside {2, 3};\n"
         "  assign done = tick inside {2, 3};\n"
         "  assign late = tick inside {2};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

// §16.12.7: `req |-> gnt` evaluates the consequent at the end point of each
// match of the antecedent, here the same tick, and is true where the
// antecedent has no match: true at 1, 3 and 4 and false at 2.
TEST(ImplicationProperty, OverlappedConsequentBeginsAtTheMatchEndPoint) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) req |-> gnt) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 1u);
}

// §16.12.7: `req |=> gnt` begins the consequent at the tick after the
// match's end point: the attempts from 1 and 2 fail at 2 and 3, the one
// from 3 has no match and is true, and the one from 4, its consequent
// beginning at a tick the run never reaches, is true when the run ends.
TEST(ImplicationProperty, NonoverlappedConsequentBeginsAtTheNextTick) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) req |=> gnt) "
                        "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 2u);
}

// §16.12.7: the consequent is evaluated separately for each match of the
// antecedent and the implication is true only where every one is: `(req
// ##[1:2] ack) |-> done` from 1 has matches ending at 2 and 3 with done at
// both and is true once the antecedent can match no more, at 3, while with
// late, low at 3, the second consequent fails the implication there; the
// attempt from 4, its antecedent unfinished at the end of the run, is true
// then.
TEST(ImplicationProperty, EveryMatchOfTheAntecedentMustHold) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) (req ##[1:2] "
                        "ack) |-> done) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(passes->value.ToUint64(), 4u);
  SimFixture g;
  auto* one_fails = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) (req ##[1:2] "
                        "ack) |-> late) passes++; else fails++;\n"),
      g, "passes");
  ASSERT_NE(one_fails, nullptr);
  EXPECT_EQ(one_fails->value.ToUint64(), 1u);
  EXPECT_EQ(g.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

// §16.12.7: the consequent may be any property, an if-else or a sequence
// among them: `req |-> gnt or ack` is true where a match's end point has
// gnt or ack, true at every tick here.
TEST(ImplicationProperty, ConsequentIsAnyProperty) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      ImplicationSource("  p: assert property (@(posedge clk) req |-> gnt or "
                        "ack) passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 0u);
}

}  // namespace
