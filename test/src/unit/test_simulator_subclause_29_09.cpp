#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// §29.9 "Mixing level-sensitive and edge-sensitive descriptions". When a UDP
// table combines both kinds of rows, the LRM fixes how a single input change is
// resolved:
//   (1) the edge-sensitive cases are processed first, then the level-sensitive
//       cases, and
//   (2) when an edge-sensitive case and a level-sensitive case both match the
//       change but call for different outputs, the level-sensitive case wins.
//
// These are simulation-stage rules carried by the production evaluator
// (UdpEvalState::EvaluateWithEdge, src/simulator/udp_eval.cpp): it collects the
// first matching edge row's output and the first matching level row's output
// separately, and a matching level row's output takes precedence over a
// matching edge row's. The table those rules operate on is *produced* by
// parsing a real UDP -- the reg output declaration is §29.3.2, the transition
// symbols are §29.6, the level symbols/`-` hold are §29.5. So every test below
// builds the primitive from real source and drives the production evaluator,
// rather than hand-assembling a UdpDecl.
//
// UDP evaluation is not yet wired into the full simulator scheduler, so the one
// synthetic step is the stimulus handed to the evaluator: the positional input
// vector plus the index/prior value of the input that transitioned. The UdpDecl
// is arena-owned by the ParseResult and outlives the UdpEvalState.

// Minimal two-row mix that puts an edge row and a level row in direct conflict.
// Inputs after q are (clk, d). The edge row fires 1 on a rising clk; the level
// row fires 0 whenever d == 1. When clk rises while d == 1 both match and
// disagree -- the level row's 0 must win.
constexpr const char* kLvlDomEdgeFirst =
    "primitive lvl_dom (q, clk, d);\n"
    "  output q; reg q;\n"
    "  input clk, d;\n"
    "  table\n"
    "  // clk d : state : next\n"
    "    r ? : ? : 1 ;   // edge-sensitive: rising clk -> 1\n"
    "    ? 1 : ? : 0 ;   // level-sensitive: d == 1 -> 0\n"
    "  endtable\n"
    "endprimitive\n";

// Same two rows, level row listed first. Resolution is by row *kind*, not table
// position, so the conflict must still resolve to the level row's output.
constexpr const char* kLvlDomLevelFirst =
    "primitive lvl_dom (q, clk, d);\n"
    "  output q; reg q;\n"
    "  input clk, d;\n"
    "  table\n"
    "    ? 1 : ? : 0 ;   // level-sensitive: d == 1 -> 0\n"
    "    r ? : ? : 1 ;   // edge-sensitive: rising clk -> 1\n"
    "  endtable\n"
    "endprimitive\n";

const UdpDecl& ParseSingleUdp(const ParseResult& r) {
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  return *r.cu->udps[0];
}

// §29.9 rule (2): edge and level cases matching the same change disagree, and
// the level-sensitive output determines the result. clk rises 0->1 while d ==
// 1: the edge row would drive 1, the level row drives 0, and 0 must win.
TEST(MixedUdpEvaluation, LevelSensitiveCaseDominatesConflictingEdge) {
  auto r = Parse(kLvlDomEdgeFirst);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'0', '1'});  // clk=0, d=1
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');
}

// §29.9 rule (1) in isolation: when only the edge case matches a change (no
// level case matches), the edge-sensitive output is used. clk rises 0->1 while
// d == 0: only the edge row matches, so the output is the edge row's 1.
TEST(MixedUdpEvaluation, EdgeCaseDrivesOutputWhenNoLevelCaseMatches) {
  auto r = Parse(kLvlDomEdgeFirst);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'0', '0'});  // clk=0, d=0
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0'}, 0, '0'), '1');
}

// §29.9 rule (2) is by row kind, not table order: with the level row listed
// first the same conflict must still resolve to the level output. Guards
// against a "last matching row wins" resolution.
TEST(MixedUdpEvaluation, LevelDominanceIndependentOfTableOrder) {
  auto r = Parse(kLvlDomLevelFirst);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'0', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');
}

// The clause's own worked example: a JK flip-flop with level-sensitive
// preset/clear logic and edge-sensitive clocking in one table. Input order
// after q is clock, j, k, preset, clear; active-low preset/clear (pc == 01
// presets to 1, pc == 10 clears to 0). Built from real source so the mixed
// table the evaluator resolves is the parser's output.
constexpr const char* kJkEdgeFf =
    "primitive jk_edge_ff (q, clock, j, k, preset, clear);\n"
    "  output q; reg q;\n"
    "  input clock, j, k, preset, clear;\n"
    "  table\n"
    "  // clock j k preset clear : state : next\n"
    "    ? ? ? 0 1 : ? : 1 ;   // preset logic (level-sensitive)\n"
    "    ? ? ? 1 0 : ? : 0 ;   // clear logic (level-sensitive)\n"
    "    r 1 1 1 1 : 0 : 1 ;   // toggle on rising clock (edge-sensitive)\n"
    "    r 1 1 1 1 : 1 : 0 ;\n"
    "    f ? ? ? ? : ? : - ;   // ignore falling clock edge\n"
    "    b * ? ? ? : ? : - ;   // ignore j change on steady clock\n"
    "  endtable\n"
    "endprimitive\n";

// In the mixed table, the level-sensitive preset row drives the output on a
// preset-input change while the clock is steady -- no clock edge occurs, so the
// edge-sensitive clocking rows cannot match, and the level case sets q to 1
// regardless of the current (unknown) state. This is §29.9's "whenever the
// preset/clear combination is 01, the output has value 1".
TEST(MixedUdpEvaluation, LevelPresetDrivesOutputInMixedTable) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  // clock=1, j=0, k=0, preset=1(inactive), clear=1(inactive); state unknown.
  state.SetInputs({'1', '0', '0', '1', '1'});
  // preset asserted (1->0, index 3): pc becomes 01 with steady clock.
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0', '0', '0', '1'}, 3, '1'), '1');
}

// The complementary level case: asserting clear (pc == 10) drives q to 0, again
// on a steady clock where no edge row can fire. §29.9's "whenever the preset
// and clear combination has value 10, the output has value 0".
TEST(MixedUdpEvaluation, LevelClearDrivesOutputInMixedTable) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'1', '0', '0', '1', '1'});
  // clear asserted (1->0, index 4): pc becomes 10 with steady clock.
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0', '0', '1', '0'}, 4, '1'), '0');
}

// §29.9 dominance must hold whatever §29.6 edge syntax expresses the edge row.
// Here the edge case is written as a parenthesized transition (01) rather than
// the letter r. On clk 0->1 with d == 1 the parenthesized-edge row would drive
// 1 and the level row drives 0; the level-sensitive case still wins. End-to-end
// over §29.6's parenthesized-transition form, built from real source.
constexpr const char* kParenDom =
    "primitive paren_dom (q, clk, d);\n"
    "  output q; reg q;\n"
    "  input clk, d;\n"
    "  table\n"
    "    (01) ? : ? : 1 ;   // edge via parenthesized transition -> 1\n"
    "    ?    1 : ? : 0 ;   // level-sensitive: d == 1 -> 0\n"
    "  endtable\n"
    "endprimitive\n";

TEST(MixedUdpEvaluation, LevelDominatesEdgeExpressedAsParenthesizedTransition) {
  auto r = Parse(kParenDom);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'0', '1'});  // clk=0, d=1
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');
}

// §29.9 dominance composed with §29.5's no-change (`-`) level output: when the
// dominant level row specifies `-`, the output holds its current value rather
// than taking the conflicting edge row's value. Distinct output form for the
// level case (a hold, not a fixed 0/1). The falling-edge row establishes a
// known non-x state from real source before the conflict is exercised, so the
// hold is observable rather than an x-vs-x coincidence.
constexpr const char* kLevelHold =
    "primitive lvl_hold (q, clk, d);\n"
    "  output q; reg q;\n"
    "  input clk, d;\n"
    "  table\n"
    "    r ? : ? : 1 ;   // rising clk -> 1 (edge)\n"
    "    f ? : ? : 0 ;   // falling clk -> 0 (edge, used to seed state)\n"
    "    ? 1 : ? : - ;   // level-sensitive: d == 1 -> hold current output\n"
    "  endtable\n"
    "endprimitive\n";

TEST(MixedUdpEvaluation, LevelNoChangeOutputHoldsAgainstConflictingEdge) {
  auto r = Parse(kLevelHold);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  // Seed a known state 0 via the falling-clock edge row (clk 1->0, d=0).
  state.SetInputs({'1', '0'});
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0'}, 0, '1'), '0');
  // Raise d to 1 with steady clock: only the level `-` row matches -> hold 0.
  EXPECT_EQ(state.EvaluateWithEdge({'0', '1'}, 1, '0'), '0');
  // Conflict: rising clk with d == 1. The edge row alone would drive 1, but the
  // level `-` row dominates and holds the output at 0.
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');
}

}  // namespace
