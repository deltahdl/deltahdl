#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

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
    "    ?  (?\?) : ? : - ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpEdgeSeq, RisingClockEdgeCapturesDataParenthesized) {
  auto r = Parse(kDEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  state.SetInputs({'0', '1'});
  EXPECT_EQ(state.GetOutput(), 'x');

  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');

  EXPECT_EQ(state.EvaluateWithEdge({'0', '1'}, 0, '1'), '1');

  EXPECT_EQ(state.EvaluateWithEdge({'0', '0'}, 1, '1'), '1');

  EXPECT_EQ(state.EvaluateWithEdge({'1', '0'}, 0, '0'), '0');
}

TEST(UdpEdgeSeq, UnspecifiedClockToXTransitionYieldsX) {
  auto r = Parse(kDEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  state.SetInputs({'0', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');

  EXPECT_EQ(state.EvaluateWithEdge({'x', '0'}, 0, '0'), 'x');
}

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

  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '1');
  EXPECT_EQ(state.EvaluateWithEdge({'0', '1'}, 0, '1'), '1');
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0'}, 1, '1'), '1');
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0'}, 0, '0'), '0');
}

}  // namespace
