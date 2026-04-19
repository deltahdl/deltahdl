#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpEdgeSeq, DFlipFlopFromSource) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  initial q = 1'bx;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "    ? f : ? : -;\n"
      "    * ? : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];

  UdpEvalState state(*udp);
  EXPECT_EQ(state.GetOutput(), 'x');

  state.SetInputs({'1', '0'});
  state.EvaluateWithEdge({'1', '1'}, 1, '0');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'1', '0'}, 1, '1');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'0', '0'}, 0, '1');
  EXPECT_EQ(state.GetOutput(), '1');

  state.EvaluateWithEdge({'0', '1'}, 1, '0');
  EXPECT_EQ(state.GetOutput(), '0');
}

// A row may describe at most one input transition; two parenthesized edge
// indicators in the same row is the example the LRM calls out as illegal.
TEST(UdpEdgeSeq, TwoParenthesizedEdgeIndicatorsInRowRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01) (10) 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Two single-letter edge symbols in the same row likewise describe more than
// one input transition.
TEST(UdpEdgeSeq, TwoSingleLetterEdgeSymbolsInRowRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b);\n"
      "  table\n"
      "    r f : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// Mixing a single-letter edge symbol with a parenthesized edge in the same
// row still describes two transitions, which is illegal.
TEST(UdpEdgeSeq, MixedEdgeSymbolAndParenthesizedEdgeInRowRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input a, input b);\n"
      "  table\n"
      "    r (01) : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(r.has_errors);
}

// A single edge indicator is the common and legal case.
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

}  // namespace
