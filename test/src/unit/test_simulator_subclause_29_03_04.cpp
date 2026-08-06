#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// §29.3.4 rule S9 — "All combinations of input values that are not explicitly
// specified result in a default output state of x" — is a runtime rule: it
// governs what the primitive drives when the current inputs miss every table
// row. Its input (the state table) is *produced* by parsing a real UDP whose
// header and port declarations come from the §29.3.1/§29.3.2 dependencies, so
// these tests build the primitive from real source syntax and then run the
// production evaluator (UdpEvalState), rather than hand-assembling a table.
//
// UDP evaluation is not yet wired into the full simulator scheduler, so the
// pipeline here is: parse real source -> pull the elaborated UdpDecl ->
// evaluate. The UdpDecl is arena-owned by the ParseResult, which the caller
// keeps alive for the lifetime of the UdpEvalState.

TEST(UdpStateTable, UnspecifiedInputCombinationDefaultsToX) {
  // Only the "0 0" and "1 1" combinations are listed; "0 1" and "1 0" are not,
  // so the primitive drives the default x for those.
  auto r = Parse(
      "primitive and2(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'1', '0'}), 'x');
}

TEST(UdpStateTable, CombinationalExplicitAllXRowProducesX) {
  // An explicitly listed all-x row (permitted by S8: all-x inputs must give an
  // x output) is honored by the runtime just like any other specified row.
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "    x x : x;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'x', 'x'}), 'x');
}

}  // namespace
