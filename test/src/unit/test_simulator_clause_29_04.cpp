#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// §29.4 "Combinational UDPs" states three runtime rules for a UDP whose output
// is not declared reg (i.e. it carries no current-state field):
//
//   * the output is a function solely of the *current* input states, so the
//     primitive holds no memory between evaluations (Claim 1);
//   * whenever an input changes the UDP is re-evaluated and the output is set
//     to the value of the state-table row that matches all current inputs
//     (Claim 2); and
//   * any input combination that is not explicitly given a row drives the
//     output to the unknown value x (Claim 3).
//
// These are simulation-stage rules carried by the production evaluator
// (UdpEvalState in src/simulator/udp_eval.cpp). The table that the rules match
// against is *produced* by parsing a real UDP: its header and port
// declarations come from §29.3.2 and its table-entry symbols (including the
// `?` abbreviation) from §29.3.4/§29.3.6. So every test below builds the
// primitive from §29.4's own multiplexer example as real source and then runs
// the production evaluator, rather than hand-assembling a UdpTableRow table.
//
// UDP evaluation is not yet wired into the full simulator scheduler, so the
// only synthetic step is the input vector handed to the evaluator; the inputs
// are positional and follow the header order (control, dataA, dataB). The
// UdpDecl is arena-owned by the ParseResult, which the caller keeps alive for
// the lifetime of the UdpEvalState.

// §29.4's multiplexer with two data inputs and a control input, written with
// the literal 0/1/x rows exactly as the clause presents them.
constexpr const char* kMultiplexer =
    "primitive multiplexer (mux, control, dataA, dataB);\n"
    "  output mux;\n"
    "  input control, dataA, dataB;\n"
    "  table\n"
    "  // control dataA dataB : mux\n"
    "    0 1 0 : 1;\n"
    "    0 1 1 : 1;\n"
    "    0 1 x : 1;\n"
    "    0 0 0 : 0;\n"
    "    0 0 1 : 0;\n"
    "    0 0 x : 0;\n"
    "    1 0 1 : 1;\n"
    "    1 1 1 : 1;\n"
    "    1 x 1 : 1;\n"
    "    1 0 0 : 0;\n"
    "    1 1 0 : 0;\n"
    "    1 x 0 : 0;\n"
    "    x 0 0 : 0;\n"
    "    x 1 1 : 1;\n"
    "  endtable\n"
    "endprimitive\n";

// Claim 2: an input combination that appears in the table drives the output to
// that row's value. Includes the clause's own "first entry" walk-through:
// control=0, dataA=1, dataB=0 selects dataA, so mux is 1.
TEST(UdpCombinational, SpecifiedRowDrivesTabledOutput) {
  auto r = Parse(kMultiplexer);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  // First table entry: control 0 selects dataA (=1) -> mux 1.
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
  // control 0 selects dataA (=0) -> mux 0.
  EXPECT_EQ(state.Evaluate({'0', '0', '1'}), '0');
  // control 1 selects dataB (=1) -> mux 1.
  EXPECT_EQ(state.Evaluate({'1', '0', '1'}), '1');
  // control 1 selects dataB (=0) -> mux 0.
  EXPECT_EQ(state.Evaluate({'1', '1', '0'}), '0');
  // A specified row may itself carry an x input: control 0, dataA 1, dataB x.
  EXPECT_EQ(state.Evaluate({'0', '1', 'x'}), '1');
}

// Claim 3: a combination with no matching row drives the output to x. This is
// the clause's explicit 0xx case (control=0, dataA=x, dataB=x): no row keys
// dataA on x, so the lookup falls through to the default unknown value.
TEST(UdpCombinational, UnspecifiedCombinationDrivesX) {
  auto r = Parse(kMultiplexer);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  // The clause's own 0xx example.
  EXPECT_EQ(state.Evaluate({'0', 'x', 'x'}), 'x');
  // Any other unlisted combination is equally unspecified: control x with
  // mismatched data has no row.
  EXPECT_EQ(state.Evaluate({'x', 'x', 'x'}), 'x');
  EXPECT_EQ(state.Evaluate({'x', '0', '1'}), 'x');
}

// Claim 1: the output is a pure function of the current inputs, with no memory
// of prior evaluations. Feeding a 1-producing row, then a 0-producing row,
// then the first row again returns the original value each time.
TEST(UdpCombinational, OutputHasNoMemoryBetweenEvaluations) {
  auto r = Parse(kMultiplexer);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0', '0'}), '0');
  // Re-presenting the first combination yields 1 again: no dependence on the
  // intervening evaluation.
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
  // And an unspecified combination in between does not stick either.
  EXPECT_EQ(state.Evaluate({'0', 'x', 'x'}), 'x');
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
}

// §29.4 also shows the multiplexer abbreviated with the `?` symbol (from
// §29.3.4/§29.3.6), noting `? = 0 1 x`. Parsing the abbreviated table and
// evaluating it exercises the same combinational rules: `?` in an input
// position matches every value, so the abbreviated form yields the same
// outputs as the literal form for the specified combinations, and a leading
// non-wildcard mismatch is still unspecified -> x.
constexpr const char* kMultiplexerAbbreviated =
    "primitive multiplexer (mux, control, dataA, dataB);\n"
    "  output mux;\n"
    "  input control, dataA, dataB;\n"
    "  table\n"
    "  // control dataA dataB : mux\n"
    "    0 1 ? : 1;\n"
    "    0 0 ? : 0;\n"
    "    1 ? 1 : 1;\n"
    "    1 ? 0 : 0;\n"
    "    x 0 0 : 0;\n"
    "    x 1 1 : 1;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpCombinational, AbbreviatedTableMatchesQuestionMark) {
  auto r = Parse(kMultiplexerAbbreviated);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  // `0 1 ?` covers dataB in {0, 1, x}, all producing mux 1.
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '1', 'x'}), '1');
  // `1 ? 1` covers dataA in {0, 1, x}, producing mux 1.
  EXPECT_EQ(state.Evaluate({'1', '0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', 'x', '1'}), '1');
  // A control=0, dataA=x combination is not covered by any row (the leading
  // literal positions demand an exact match) -> x.
  EXPECT_EQ(state.Evaluate({'0', 'x', '0'}), 'x');
}

// A combinational table may also key an input on the `b` symbol (from
// §29.3.4/§29.3.6), which iterates over 0 and 1 but — unlike `?` — does not
// cover x. Evaluating such a table exercises the same §29.4 rules on a distinct
// input form: Claim 2 (a `b` row matches a 0 or 1 input and drives the tabled
// output) and Claim 3 (an x input matches no `b` row, so the combination is
// unspecified and the output is x). Built from real source so the parsed table
// carries the actual `b` symbol into the production evaluator.
constexpr const char* kSelectB =
    "primitive sel (y, a, c);\n"
    "  output y;\n"
    "  input a, c;\n"
    "  table\n"
    "  // a c : y\n"
    "    b 1 : 1;\n"
    "    b 0 : 0;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpCombinational, BInputSymbolMatchesZeroAndOneNotX) {
  auto r = Parse(kSelectB);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  // Claim 2: `b 1` matches a in {0, 1} when c is 1 -> tabled output 1.
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  // `b 0` matches a in {0, 1} when c is 0 -> tabled output 0.
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '0');
  // Claim 3: `b` does not cover x, so an x on the first input matches no row
  // and the output becomes the default unknown value.
  EXPECT_EQ(state.Evaluate({'x', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'x', '0'}), 'x');
}

}  // namespace
