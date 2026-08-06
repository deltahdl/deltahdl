#include "fixture_parser.h"

using namespace delta;

namespace {

// §29.6: a table entry may carry a transition specification on at most one
// input. Entries with two transitions, e.g. "(01)(01)0 : 0 : 1;", are illegal.
// The parser rejects any row whose input field holds more than one edge.

TEST(UdpEdgeSeq, SingleEdgeIndicatorInRowAccepted) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpEdgeSeq, TwoParenthesizedEdgeIndicatorsInRowRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01) (10) 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// §29.6 names two ways to write a transition: a parenthesized pair such as
// (01) or a single transition symbol such as `r`. The at-most-one-transition
// rule must recognize the letter-symbol form as an edge too, so a row bearing
// two letter edges is rejected the same way as two parenthesized edges. This
// drives the count rule over the letter-symbol operand kind -- a different
// token path from the parenthesized form, and the only case that observes the
// counter treating a bare letter as a transition.
TEST(UdpEdgeSeq, TwoLetterEdgeSymbolsInRowRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b);\n"
      "  table\n"
      "    r f : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
