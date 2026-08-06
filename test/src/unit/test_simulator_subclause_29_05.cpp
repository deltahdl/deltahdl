#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// §29.5 "Level-sensitive sequential UDPs" describes how a UDP whose output is
// declared reg evaluates. Its runtime rules, relative to a combinational UDP,
// are:
//
//   * the presence of a reg output makes the primitive sequential, so it holds
//     an internal state between evaluations and its output value is always the
//     same as that internal state;
//   * each table entry carries an extra current-state field, and that field
//     represents the current state of the UDP -- so which row applies depends
//     on the present output as well as on the inputs; and
//   * the output field of a matched row is the *next* state, and the no-change
//     symbol `-` in that field leaves the state (and hence the output)
//     unchanged.
//
// These are simulation-stage rules carried by the production evaluator
// (UdpEvalState in src/simulator/udp_eval.cpp): a reg output sets
// is_sequential, MatchState compares each row's current-state field against the
// held output, and ResolveOutput maps `-` to the current output. The table the
// rules match against is *produced* by parsing a real UDP: the reg output
// declaration comes from §29.3.2, the current-state field and its symbols (`?`,
// `-`) from §29.3.4/§29.3.6. So every test below builds the primitive from
// §29.5's own latch example (or a close variant) as real source and then runs
// the production evaluator, rather than hand-assembling a UdpTableRow table.
//
// UDP evaluation is not yet wired into the full simulator scheduler, so the
// only synthetic step is the positional input vector handed to the evaluator;
// the inputs follow the header order after the output. The UdpDecl is
// arena-owned by the ParseResult, which the caller keeps alive for the lifetime
// of the UdpEvalState.

// §29.5's latch example, written exactly as the clause presents it: a non-ANSI
// header with a separate `reg q;` declaration and a three-part table entry
// (inputs : current-state : next-state). Input order after the output q is
// (ena_, data).
constexpr const char* kLatch =
    "primitive latch (q, ena_, data);\n"
    "  output q; reg q;\n"
    "  input ena_, data;\n"
    "  table\n"
    "  // ena_ data : q : q+\n"
    "    0 1 : ? : 1 ;\n"
    "    0 0 : ? : 0 ;\n"
    "    1 ? : ? : - ;  // - = no change\n"
    "  endtable\n"
    "endprimitive\n";

// The reg output makes the primitive sequential and gives it an internal state
// that the output value always tracks. With ena_ low the latch is transparent
// (q follows data); with ena_ high the `-` row holds the state, so the output
// keeps its previous value across evaluations -- memory the combinational form
// does not have.
TEST(UdpLevelSeq, RegOutputHoldsStateAndTracksIt) {
  auto r = Parse(kLatch);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  // No initial statement, so the internal state (and output) starts unknown.
  EXPECT_EQ(state.GetOutput(), 'x');

  // ena_=0 opens the latch: q follows data.
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');

  // ena_=1 closes the latch: the `-` row holds. The output keeps its value
  // even as data changes underneath -- the state persists between evaluations.
  EXPECT_EQ(state.Evaluate({'1', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '0');
  EXPECT_EQ(state.GetOutput(), '0');

  // Re-open, capture a 1, then hold it high: the held state can be either
  // value.
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(state.GetOutput(), '1');
}

// The output field of a matched row is the next state. When ena_ is low the
// latch's output field carries the literal next value (1 or 0), and the output
// updates to exactly that on each evaluation.
TEST(UdpLevelSeq, OutputFieldIsNextState) {
  auto r = Parse(kLatch);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  // Each transparent evaluation drives the output to its row's next-state
  // field, regardless of the prior state.
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
}

// The `-` symbol in the output field means "no change": a matched hold row
// leaves the state (and output) at its current value rather than driving a new
// one. Contrast with the default-x behavior: here the row *does* match, so the
// output is the held value, not x.
TEST(UdpLevelSeq, NoChangeOutputSymbolHoldsCurrentState) {
  auto r = Parse(kLatch);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  // Establish a known state of 1.
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  // The `1 ? : ? : -` row matches while holding; the `-` keeps the output at 1
  // through several evaluations that vary data.
  EXPECT_EQ(state.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '1');
}

// The current-state field represents the current state, so an otherwise
// identical input can select different rows -- and thus different next states
// -- depending on the held output. This primitive keys two rows on the same
// input (s=0) but distinct current-state fields, proving the field is matched
// against the live state.
constexpr const char* kStateKeyed =
    "primitive cs (q, s);\n"
    "  output q; reg q;\n"
    "  input s;\n"
    "  table\n"
    "  // s : q : q+\n"
    "    1 : ? : 0 ;\n"  // s high clears, regardless of current state
    "    0 : 0 : 1 ;\n"  // s low, currently 0 -> advance to 1
    "    0 : 1 : - ;\n"  // s low, currently 1 -> hold
    "  endtable\n"
    "endprimitive\n";

TEST(UdpLevelSeq, CurrentStateFieldSelectsRow) {
  auto r = Parse(kStateKeyed);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  // Clear to a known state of 0.
  EXPECT_EQ(state.Evaluate({'1'}), '0');
  // s=0 with current state 0 selects the advance row -> 1.
  EXPECT_EQ(state.Evaluate({'0'}), '1');
  // s=0 again, but now current state is 1, selects the hold row -> stays 1.
  // Same input, different row, purely because the current-state field matched
  // the live state.
  EXPECT_EQ(state.Evaluate({'0'}), '1');
  EXPECT_EQ(state.Evaluate({'0'}), '1');
  // Clearing brings it back, confirming the state genuinely round-trips.
  EXPECT_EQ(state.Evaluate({'1'}), '0');
  EXPECT_EQ(state.Evaluate({'0'}), '1');
}

// The current-state field is matched against the held state the same way an
// input field is matched against its input, so it accepts the abbreviation
// symbols. A `b` current-state field (from §29.3.6) covers a held 0 or 1 but --
// unlike `?` -- not a held x. This exercises a distinct matching branch for
// §29.5's "the field represents the current state" rule: the row applies only
// when the live state is 0 or 1, and is skipped (falling through to the default
// x) when the state is x. Built from real source so the parsed current-state
// field carries the actual `b` symbol into the production evaluator.
constexpr const char* kBStateKeyed =
    "primitive bcs (q, s);\n"
    "  output q; reg q;\n"
    "  input s;\n"
    "  table\n"
    "  // s : q : q+\n"
    "    0 : b : 1 ;\n"  // s low, current state 0 or 1 -> next 1
    "    1 : ? : 0 ;\n"  // s high clears to 0 from any state
    "  endtable\n"
    "endprimitive\n";

TEST(UdpLevelSeq, CurrentStateFieldBMatchesZeroAndOneNotX) {
  auto r = Parse(kBStateKeyed);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  // Negative form: the held state is x, which `b` does not cover. The `b` row
  // is skipped and no other row keys on s=0, so the combination is unspecified
  // and the output stays at the default unknown value.
  EXPECT_EQ(state.GetOutput(), 'x');
  EXPECT_EQ(state.Evaluate({'0'}), 'x');
  // Clear to a known held state of 0.
  EXPECT_EQ(state.Evaluate({'1'}), '0');
  // Positive: `b` matches the held 0, selecting the row -> next 1.
  EXPECT_EQ(state.Evaluate({'0'}), '1');
  // Positive: `b` also matches the held 1. The row applies again and re-drives
  // 1; that the output is 1 (not the default x) proves the `b` field matched
  // the held state rather than the row being skipped.
  EXPECT_EQ(state.Evaluate({'0'}), '1');
}

}  // namespace
