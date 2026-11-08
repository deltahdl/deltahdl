#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

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

TEST(MixedUdpEvaluation, LevelSensitiveCaseDominatesConflictingEdge) {
  auto r = Parse(kLvlDomEdgeFirst);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'0', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');
}

TEST(MixedUdpEvaluation, EdgeCaseDrivesOutputWhenNoLevelCaseMatches) {
  auto r = Parse(kLvlDomEdgeFirst);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'0', '0'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0'}, 0, '0'), '1');
}

TEST(MixedUdpEvaluation, LevelDominanceIndependentOfTableOrder) {
  auto r = Parse(kLvlDomLevelFirst);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'0', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');
}

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

TEST(MixedUdpEvaluation, LevelPresetDrivesOutputInMixedTable) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'1', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0', '0', '0', '1'}, 3, '1'), '1');
}

TEST(MixedUdpEvaluation, LevelClearDrivesOutputInMixedTable) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'1', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0', '0', '1', '0'}, 4, '1'), '0');
}

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
  state.SetInputs({'0', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');
}

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
  state.SetInputs({'1', '0'});
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0'}, 0, '1'), '0');
  EXPECT_EQ(state.EvaluateWithEdge({'0', '1'}, 1, '0'), '0');
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');
}

}  // namespace
