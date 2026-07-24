#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// §29.3.5 second sentence — "The z values passed to UDP inputs shall be treated
// the same as x values" — is a runtime rule: it governs how the primitive
// evaluates when a z arrives on an input terminal. The table the rule matches
// against is *produced* by parsing a real UDP whose header, port declarations,
// and state table come from the §29.3.2/§29.3.4 dependencies, so these tests
// build the primitive from real source syntax and then run the production
// evaluator (UdpEvalState), rather than hand-assembling a table.
//
// UDP evaluation is not yet wired into the full simulator scheduler, so the
// only synthetic step is the input vector handed to the evaluator; there is no
// way to drive a z onto a terminal through the scheduler yet. The UdpDecl is
// arena-owned by the ParseResult, which the caller keeps alive for the lifetime
// of the UdpEvalState.
//
// (The companion compile-time half of §29.3.5 — "a z in a table entry is
// illegal" — is a parse-stage rule and is observed in the parser test file.)

TEST(UdpInputZAsX, CombinationalZMatchesXRow) {
  // A row keyed on x matches an input that arrives as z, because z is coerced
  // to x before the level comparison.
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'z', '0'}), '1');
}

TEST(UdpInputZAsX, CombinationalBRowRejectsCoercedZ) {
  // b matches only 0 and 1. A z coerced to x does not match b, so the input
  // combination is unspecified and the primitive drives the default x.
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    b 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'z', '1'}), 'x');
}

TEST(UdpInputZAsX, SequentialEdgeZTreatedAsX) {
  // A z arriving on the edge terminal is coerced to x, so a 0->z transition is
  // seen as the 0->x edge that the p edge symbol accepts.
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    p ? : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), '0');
  state.SetInputs({'0', '0'});
  state.EvaluateWithEdge({'z', '0'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpInputZAsX, SequentialPreviousZTreatedAsX) {
  // A z that was the previous value on the edge terminal is coerced to x, so a
  // z->0 transition is seen as the x->0 edge that the n edge symbol accepts.
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    n ? : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), '1');
  state.SetInputs({'z', '1'});
  state.EvaluateWithEdge({'0', '1'}, 0, 'z');
  EXPECT_EQ(state.GetOutput(), '0');
}

}  // namespace
