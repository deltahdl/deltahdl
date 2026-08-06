#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

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

}  // namespace
