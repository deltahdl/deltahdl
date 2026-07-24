#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

// §29.7 Sequential UDP initialization (simulation-start semantics).
//
// §29.7 states two runtime rules about the optional initial statement of a
// sequential UDP:
//
//   * the value the initial statement assigns is the output's value at the
//     start of simulation, and an instance delay does not delay this
//     assignment (the value is applied immediately, at time 0); and
//   * that same value is the current state in the state table when simulation
//     starts, so it participates in row selection on the first evaluation.
//
// Both rules are carried by the production evaluator UdpEvalState
// (src/simulator/udp_eval.cpp): its constructor seeds output_ from the recorded
// initial value with no delay parameter, and MatchState then compares each
// row's current-state field against that seeded output.
//
// The value UdpEvalState operates on -- has_initial and initial_value -- is
// *produced* by parsing an `initial` statement (the reg output declaration from
// §29.3.2, the value literal from §29.3.3, the current-state field from
// §29.3.4). So every test below builds the primitive from real UDP source and
// runs the production evaluator, rather than hand-assembling a UdpDecl. UDP
// evaluation is not yet wired into the full simulator scheduler, so the only
// synthetic step is the positional input vector; the inputs follow the header
// order after the output. The UdpDecl is arena-owned by the ParseResult, kept
// alive for the lifetime of the UdpEvalState.

namespace {

// §29.7 Example 1: the srff sequential UDP with `initial q = 1'b1;`. The output
// q takes the value 1 at the start of simulation. An instance delay does not
// delay this -- the value is present immediately, so GetOutput() returns it
// before any evaluation drives the table.
constexpr const char* kSrff =
    "primitive srff (q, s, r);\n"
    "  output q; reg q;\n"
    "  input s, r;\n"
    "  initial q = 1'b1;\n"
    "  table\n"
    "  // s r  q  q+\n"
    "    1 0 : ? : 1 ;\n"
    "    f 0 : 1 : - ;\n"
    "    0 r : ? : 0 ;\n"
    "    0 f : 0 : - ;\n"
    "    1 1 : ? : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpInitialStatement, InitialValueIsOutputAtSimulationStart) {
  auto r = Parse(kSrff);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
  EXPECT_TRUE(r.cu->udps[0]->has_initial);

  // The evaluator seeds the output from the parsed initial value at
  // construction (simulation start), with no delay involved: the value is
  // available immediately, before the first evaluation.
  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), '1');
}

// The initial statement is optional. Parsed from real source with no initial
// statement, the sequential UDP starts in the unknown state rather than taking
// a specified value -- the evaluator only seeds a value when has_initial is
// set. This is §29.7's "the initial statement is optional" observed at runtime.
constexpr const char* kSrffNoInitial =
    "primitive srff (q, s, r);\n"
    "  output q; reg q;\n"
    "  input s, r;\n"
    "  table\n"
    "  // s r  q  q+\n"
    "    1 0 : ? : 1 ;\n"
    "    0 r : ? : 0 ;\n"
    "    1 1 : ? : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpInitialStatement, OptionalInitialLeavesOutputUnknown) {
  auto r = Parse(kSrffNoInitial);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
  EXPECT_FALSE(r.cu->udps[0]->has_initial);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), 'x');
}

// The permitted start value 1'bx flows through the same seeding as 1 and 0:
// unlike the no-initial case, has_initial is set here, so the evaluator seeds
// the output from the recorded 'x' value rather than defaulting it. The
// observable output is the same unknown value, but it arrives via the seeded
// path -- the explicit x is carried from the parsed initial statement, not
// ignored.
constexpr const char* kSrffInitX =
    "primitive srff (q, s, r);\n"
    "  output q; reg q;\n"
    "  input s, r;\n"
    "  initial q = 1'bx;\n"
    "  table\n"
    "  // s r  q  q+\n"
    "    1 0 : ? : 1 ;\n"
    "    0 r : ? : 0 ;\n"
    "    1 1 : ? : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpInitialStatement, InitialValueXSeedsUnknownStartState) {
  auto r = Parse(kSrffInitX);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
  // The initial statement is present (the x is an explicit start value), which
  // is the code path this exercises -- distinct from the no-initial default.
  EXPECT_TRUE(r.cu->udps[0]->has_initial);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), 'x');
}

// The initial value is the current state in the state table at simulation
// start. This primitive keys two rows on the same input level (s=0) but
// distinct current-state fields, so the only thing that decides which row
// applies on the first evaluation -- and thus the first output -- is the seeded
// current state. The two source strings differ solely in the initial value
// (1'b1 vs 1'b0), so the differing first output isolates the initial
// statement's role as the current state.
constexpr const char* kHoldInitOne =
    "primitive hold (q, s);\n"
    "  output q; reg q;\n"
    "  input s;\n"
    "  initial q = 1'b1;\n"
    "  table\n"
    "  // s : q : q+\n"
    "    0 : 1 : 1 ;\n"  // s low, current state 1 -> stays 1
    "    0 : 0 : 0 ;\n"  // s low, current state 0 -> stays 0
    "  endtable\n"
    "endprimitive\n";

constexpr const char* kHoldInitZero =
    "primitive hold (q, s);\n"
    "  output q; reg q;\n"
    "  input s;\n"
    "  initial q = 1'b0;\n"
    "  table\n"
    "  // s : q : q+\n"
    "    0 : 1 : 1 ;\n"
    "    0 : 0 : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpInitialStatement, InitialValueServesAsCurrentState) {
  auto high = Parse(kHoldInitOne);
  ASSERT_NE(high.cu, nullptr);
  EXPECT_FALSE(high.has_errors);
  ASSERT_EQ(high.cu->udps.size(), 1u);

  auto low = Parse(kHoldInitZero);
  ASSERT_NE(low.cu, nullptr);
  EXPECT_FALSE(low.has_errors);
  ASSERT_EQ(low.cu->udps.size(), 1u);

  // Seeded state 1 selects the "current state 1" row on the first evaluation.
  UdpEvalState state_high(*high.cu->udps[0]);
  EXPECT_EQ(state_high.GetOutput(), '1');
  EXPECT_EQ(state_high.Evaluate({'0'}), '1');

  // Seeded state 0 selects the "current state 0" row instead -- same input, the
  // initial value alone changes which row matches.
  UdpEvalState state_low(*low.cu->udps[0]);
  EXPECT_EQ(state_low.GetOutput(), '0');
  EXPECT_EQ(state_low.Evaluate({'0'}), '0');
}

}  // namespace
