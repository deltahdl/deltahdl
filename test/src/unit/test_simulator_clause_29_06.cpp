#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// §29.6 "Edge-sensitive sequential UDPs". Unlike a level-sensitive UDP, whose
// output is determined by the input levels and the current state alone, an
// edge-sensitive UDP changes its output only in response to a specific
// transition of an input. That turns the state table into a transition table:
// a row fires when the designated input makes the transition the row names.
//
// These are simulation-stage rules carried by the production evaluator
// (UdpEvalState in src/simulator/udp_eval.cpp): EvaluateWithEdge matches each
// row's transition field against the (prev,new) value pair of the input that
// changed, and when no row matches the changed transition the output falls to
// the default unknown value. The table those rules operate on is *produced* by
// parsing a real UDP -- the reg output declaration is §29.3.2, the transition
// symbols and level abbreviations (r, f, (01), (0?), (??), ?, -) are
// §29.3.4/§29.3.6. So every test below builds the primitive from real source
// and runs the production evaluator, rather than hand-assembling a table.
//
// UDP evaluation is not yet wired into the full simulator scheduler, so the
// only synthetic step is the stimulus handed to the evaluator: the positional
// input vector plus the index/prior-value of the input that transitioned. The
// UdpDecl is arena-owned by the ParseResult, kept alive for the lifetime of the
// UdpEvalState.

// §29.6's own example: a rising-edge D flip-flop written with parenthesized
// edge transitions, exactly as the clause presents it (non-ANSI header with a
// separate `reg q;`). Input order after the output q is (clock, data). The
// (01) rows sample data on the rising clock edge; the (0?)/(?0)/(??) rows keep
// the state on the transitions that must not disturb the output.
constexpr const char* kDEdgeFf =
    "primitive d_edge_ff (q, clock, data);\n"
    "  output q; reg q;\n"
    "  input clock, data;\n"
    "  table\n"
    "  // clock  data   q   q+\n"
    "  // obtain output on rising edge of clock\n"
    "    (01) 0   : ? : 0 ;\n"
    "    (01) 1   : ? : 1 ;\n"
    "    (0?) 1   : 1 : 1 ;\n"
    "    (0?) 0   : 0 : 0 ;\n"
    "  // ignore negative edge of clock\n"
    "    (?0) ?   : ? : - ;\n"
    "  // ignore data changes on steady clock\n"
    "    ?  (??) : ? : - ;\n"
    "  endtable\n"
    "endprimitive\n";

// The edge-sensitive UDP samples data only on the rising edge of clock; on the
// falling edge and on data changes while clock is steady it holds -- those
// non-disturbing transitions are explicitly given `-` rows so they do not drive
// the output to x. Built from §29.6's own parenthesized example, driven through
// the production evaluator.
TEST(UdpEdgeSeq, RisingClockEdgeCapturesDataParenthesized) {
  auto r = Parse(kDEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  // clock=0, data=1 to start; no initial statement, so the state is unknown.
  state.SetInputs({'0', '1'});
  EXPECT_EQ(state.GetOutput(), 'x');

  // Rising clock (0->1) with data 1: the (01) 1 row fires -> capture 1.
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');

  // Falling clock (1->0): the (?0) row holds via `-`; the captured 1 stays.
  EXPECT_EQ(state.EvaluateWithEdge({'0', '1'}, 0, '1'), '1');

  // Data change while clock steady at 0 (input 1 goes 1->0): the ? (??) row
  // holds via `-`; the output is undisturbed.
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0'}, 1, '1'), '1');

  // Rising clock again, now with data 0: the (01) 0 row fires -> capture 0.
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0'}, 0, '0'), '0');
}

// §29.6, verbatim consequence stated by the clause: a clock transition of 0->x
// with data 0 and current state 1 leaves no matching row, so the output goes to
// x. None of the (01)/(0?) rows admit a new clock value of x with these
// data/state values, so the transition is unspecified and defaults to unknown.
TEST(UdpEdgeSeq, UnspecifiedClockToXTransitionYieldsX) {
  auto r = Parse(kDEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  // Bring the state to a known 1 via a specified rising edge with data 1.
  state.SetInputs({'0', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');

  // Clock 0->x with data 0 and current state 1: no row matches -> x.
  EXPECT_EQ(state.EvaluateWithEdge({'x', '0'}, 0, '0'), 'x');
}

// §29.6 admits a transition written as a single symbol such as `r` (rising) or
// `f` (falling), not only a parenthesized pair. The same rising-edge flip-flop
// expressed with letter symbols drives the evaluator's letter-edge match path,
// which is distinct production code from the parenthesized-edge match path
// exercised above -- so this is the input form that observes the letter-symbol
// edge machinery applying §29.6's edge-triggered behavior. Built from real
// source: `r`/`f`/`*` are §29.3.4 transition symbols, the reg output §29.3.2.
constexpr const char* kDEdgeFfLetters =
    "primitive d_edge_ff2 (q, clock, data);\n"
    "  output q; reg q;\n"
    "  input clock, data;\n"
    "  table\n"
    "  // clock data : q : q+\n"
    "    r 0 : ? : 0 ;\n"
    "    r 1 : ? : 1 ;\n"
    "    f ? : ? : - ;\n"
    "    ? * : ? : - ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpEdgeSeq, RisingClockEdgeCapturesDataLetterSymbols) {
  auto r = Parse(kDEdgeFfLetters);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  state.SetInputs({'0', '1'});

  // `r 1` fires on the rising clock edge -> capture 1.
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');
  // `f ?` holds via `-` on the falling clock edge; the captured 1 stays.
  EXPECT_EQ(state.EvaluateWithEdge({'0', '1'}, 0, '1'), '1');
  // `? *` holds via `-` on a data change while clock is steady.
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0'}, 1, '1'), '1');
  // `r 0` fires on the next rising edge -> capture 0.
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0'}, 0, '0'), '0');
}

}  // namespace
