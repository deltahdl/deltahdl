#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// §29.10 "Level-sensitive dominance". This subclause carries no new BNF and no
// new 'shall'; it is the worked illustration (Table 29-3) of the resolution
// rule stated in §29.9: when a single input change matches both an
// edge-sensitive row and a level-sensitive row of a mixed UDP table and the two
// specify opposite outputs, the edge case is evaluated first and the
// level-sensitive case then dominates. The rule itself lives in the production
// evaluator UdpEvalState::EvaluateWithEdge (src/simulator/udp_eval.cpp), owned
// by §29.9. What §29.10 adds is Table 29-3's specific shape, which is the
// *mirror* of the §29.9 tests: here the conflicting edge row is a `-` hold
// (whose value equals the current state 0) while the level row drives a fixed
// 1, so dominance flips a would-be hold-at-0 to 1.
//
// The table is produced by parsing a real primitive -- the reg output is
// §29.3.2, the falling-edge `f` symbol is §29.6, the `-` hold and the level
// preset/clear rows are §29.5 -- so the witness drives the production evaluator
// over the parser's own output rather than a hand-built UdpDecl. UDP evaluation
// is not yet wired into the full scheduler, so the stimulus (the positional
// input vector plus the index/prior value of the input that transitioned) is
// the one synthetic step, matching the §29.9 simulator tests.

// The jk_edge_ff primitive of §29.9/§29.10, reduced to the rows Table 29-3
// exercises: the level-sensitive preset (pc == 01 -> 1) and clear (pc == 10 ->
// 0) rows, one edge-sensitive rising-clock clocking row, and the falling-clock
// row that ignores the falling edge by holding the current state (`-`). Inputs
// after q are clock, j, k, preset, clear; preset/clear are active low, so the
// preset/clear pair "pc" is 01 to preset and 10 to clear.
constexpr const char* kJkEdgeFf =
    "primitive jk_edge_ff (q, clock, j, k, preset, clear);\n"
    "  output q; reg q;\n"
    "  input clock, j, k, preset, clear;\n"
    "  table\n"
    "  // clock j k preset clear : state : next\n"
    "    ? ? ? 0 1 : ? : 1 ;   // preset logic  (level-sensitive) pc=01 -> 1\n"
    "    ? ? ? 1 0 : ? : 0 ;   // clear logic   (level-sensitive) pc=10 -> 0\n"
    "    r 0 0 1 1 : 0 : 1 ;   // normal clocking (edge-sensitive)\n"
    "    f ? ? ? ? : ? : - ;   // ignore the falling clock edge (edge, hold)\n"
    "  endtable\n"
    "endprimitive\n";

const UdpDecl& ParseSingleUdp(const ParseResult& r) {
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  return *r.cu->udps[0];
}

// Table 29-3, the conflict case. The edge row's included case is `f 00 01 : 0 :
// 0` (clock falls, jk=00, pc=01, state 0 -> hold, i.e. 0) and the level row's
// included case is `0 00 01 : 0 : 1` (clock steady 0, pc=01, state 0 -> 1): for
// the same input/state combination they specify opposite outputs. Both match
// the single falling-clock change from a prior state of 0, and level-sensitive
// dominance must make the output 1.
//
// State 0 is first established through the primitive's own clear logic (pc=10),
// then the input vector settles to pc=01 with the clock still high (SetInputs
// records the pre-change baseline without re-running the table -- the
// per-change evaluator only re-fires on the single changed input). The falling
// clock is then the changed input: the `f` hold row alone would keep the output
// at 0, but the matching level preset row dominates and drives it to 1.
TEST(LevelSensitiveDominance, LevelPresetDominatesFallingClockHold) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  // Seed current state 0 via the level clear row (pc=10) on a steady clock.
  state.SetInputs({'1', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0', '0', '1', '0'}, 4, '1'), '0');

  // Settle the inputs to pc=01 (preset asserted) with the clock still high; the
  // stored state is still 0. This is Table 29-3's paradoxical precondition:
  // state 0 while pc=01.
  state.SetInputs({'1', '0', '0', '0', '1'});

  // The falling clock edge (index 0, 1->0). The edge `f` hold row resolves to
  // the current state 0; the level preset row resolves to 1. Level dominance
  // makes the result 1.
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '0', '1'}, 0, '1'), '1');
}

// The negative / contrast form: absent a matching level row, dominance does not
// apply and the edge case governs. With preset and clear both inactive (pc=11)
// no level row matches the falling clock, so the `f` hold row alone governs and
// the output stays at the prior state 0. This isolates that the flip to 1 above
// is caused by the dominating level row, not by the falling edge itself.
TEST(LevelSensitiveDominance, FallingClockHoldsWhenNoLevelRowMatches) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  // Seed state 0 via the clear row, then de-assert clear to pc=11 (inactive).
  state.SetInputs({'1', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0', '0', '1', '0'}, 4, '1'), '0');
  state.SetInputs({'1', '0', '0', '1', '1'});

  // Falling clock with pc=11: only the `f` hold row matches -> output holds 0.
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '1', '1'}, 0, '1'), '0');
}

// Table 29-3's other included case, in isolation: the level-sensitive row's
// case `0 00 01 : 0 : 1` (clock steady low, pc=01, state 0 -> 1). Here the
// change that fires the rule is a *level* input (asserting preset), not a clock
// edge: with the clock held at 0 no edge row can match, so the level preset row
// alone drives the output to 1. Paired with the falling-clock hold above (which
// yields 0 for the same pc=01/state-0 combination), this exhibits the opposite
// outputs of the two included cases that the dominance rule must reconcile.
TEST(LevelSensitiveDominance,
     LevelPresetIncludedCaseDrivesOneOnSteadyLowClock) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  // Seed state 0 via the clear row while the clock is low, then settle the
  // baseline to pc=11 (both inactive) without re-running the table.
  state.SetInputs({'0', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '1', '0'}, 4, '1'), '0');
  state.SetInputs({'0', '0', '0', '1', '1'});

  // Assert preset (index 3, 1->0) with the clock still low: pc becomes 01, no
  // edge occurs, and the level preset row alone drives the output to 1.
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '0', '1'}, 3, '1'), '1');
}

// Dominance is by row *kind*, not table position: §29.10's Table 29-3 lists the
// level rows before the edge row, but §29.9 also states the edge case is
// processed first regardless. Reordering the table so the falling-edge row
// precedes the level preset row must still resolve the conflict to the level
// output 1, guarding against a first/last-matching-row resolution.
constexpr const char* kJkEdgeFfEdgeFirst =
    "primitive jk_edge_ff (q, clock, j, k, preset, clear);\n"
    "  output q; reg q;\n"
    "  input clock, j, k, preset, clear;\n"
    "  table\n"
    "    f ? ? ? ? : ? : - ;   // ignore the falling clock edge (edge, hold)\n"
    "    ? ? ? 0 1 : ? : 1 ;   // preset logic (level-sensitive) pc=01 -> 1\n"
    "    ? ? ? 1 0 : ? : 0 ;   // clear logic  (level-sensitive) pc=10 -> 0\n"
    "  endtable\n"
    "endprimitive\n";

TEST(LevelSensitiveDominance, DominanceIndependentOfTableOrder) {
  auto r = Parse(kJkEdgeFfEdgeFirst);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  // Seed state 0 via the clear row, then settle to pc=01 with clock high.
  state.SetInputs({'1', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0', '0', '1', '0'}, 4, '1'), '0');
  state.SetInputs({'1', '0', '0', '0', '1'});

  // Falling clock: level preset still dominates the falling-edge hold -> 1.
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '0', '1'}, 0, '1'), '1');
}

}  // namespace
