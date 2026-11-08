#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

constexpr const char* kJkEdgeFf =
    "primitive jk_edge_ff (q, clock, j, k, preset, clear);\n"
    "  output q; reg q;\n"
    "  input clock, j, k, preset, clear;\n"
    "  table\n"
    "  // clock j k preset clear : state : next\n"
    "    ? ? ? 0 1 : ? : 1 ;   // preset logic  (level-sensitive) pc=01 -> 1\n"
    "    ? ? ? 1 0 : ? : 0 ;   // clear logic   (level-sensitive) pc=10 -> 0\n"
    "    r 0 0 1 1 : 0 : 1 ;   // normal clocking (edge-sensitive)\n"
    "    f ? ? ? ? : ? : - ;   // ignore the falling clock edge (edge, hold)\n"
    "  endtable\n"
    "endprimitive\n";

const UdpDecl& ParseSingleUdp(const ParseResult& r) {
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  return *r.cu->udps[0];
}

char FallingClockUnderAssertedPreset(const UdpDecl& udp) {
  UdpEvalState state(udp);
  state.SetInputs({'1', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0', '0', '1', '0'}, 4, '1'), '0');
  state.SetInputs({'1', '0', '0', '0', '1'});
  return state.EvaluateWithEdge({'0', '0', '0', '0', '1'}, 0, '1');
}

TEST(LevelSensitiveDominance, LevelPresetDominatesFallingClockHold) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  EXPECT_EQ(FallingClockUnderAssertedPreset(udp), '1');
}

TEST(LevelSensitiveDominance, FallingClockHoldsWhenNoLevelRowMatches) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'1', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0', '0', '1', '0'}, 4, '1'), '0');
  state.SetInputs({'1', '0', '0', '1', '1'});

  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '1', '1'}, 0, '1'), '0');
}

TEST(LevelSensitiveDominance,
     LevelPresetIncludedCaseDrivesOneOnSteadyLowClock) {
  auto r = Parse(kJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  UdpEvalState state(udp);
  state.SetInputs({'0', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '1', '0'}, 4, '1'), '0');
  state.SetInputs({'0', '0', '0', '1', '1'});

  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '0', '1'}, 3, '1'), '1');
}

constexpr const char* kJkEdgeFfEdgeFirst =
    "primitive jk_edge_ff (q, clock, j, k, preset, clear);\n"
    "  output q; reg q;\n"
    "  input clock, j, k, preset, clear;\n"
    "  table\n"
    "    f ? ? ? ? : ? : - ;   // ignore the falling clock edge (edge, hold)\n"
    "    ? ? ? 0 1 : ? : 1 ;   // preset logic (level-sensitive) pc=01 -> 1\n"
    "    ? ? ? 1 0 : ? : 0 ;   // clear logic  (level-sensitive) pc=10 -> 0\n"
    "  endtable\n"
    "endprimitive\n";

TEST(LevelSensitiveDominance, DominanceIndependentOfTableOrder) {
  auto r = Parse(kJkEdgeFfEdgeFirst);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);

  EXPECT_EQ(FallingClockUnderAssertedPreset(udp), '1');
}

}  // namespace
