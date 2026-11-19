#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_parser.h"
#include "fixture_simulator.h"
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

char EdgeAgainstLevelRow(const char* edge_row, char from, char to) {
  auto r = Parse(std::string("primitive abbrev_dom (q, clk, d);\n"
                             "  output q; reg q;\n"
                             "  input clk, d;\n"
                             "  table\n"
                             "    ") +
                 edge_row +
                 "\n"
                 "    ? 1 : ? : 0 ;\n"
                 "  endtable\n"
                 "endprimitive\n");
  if (r.cu == nullptr) return '?';
  const UdpDecl& udp = ParseSingleUdp(r);
  UdpEvalState state(udp);
  state.SetOutput('1');
  state.SetInputs({from, '1'});
  return state.EvaluateWithEdge({to, '1'}, 0, from);
}

TEST(MixedUdpEvaluation, LevelDominatesPositiveEdgeAbbreviation) {
  EXPECT_EQ(EdgeAgainstLevelRow("p ? : ? : 1 ;", '0', '1'), '0');
  EXPECT_EQ(EdgeAgainstLevelRow("p ? : ? : 1 ;", 'x', '1'), '0');
}

TEST(MixedUdpEvaluation, LevelDominatesNegativeEdgeAbbreviation) {
  EXPECT_EQ(EdgeAgainstLevelRow("n ? : ? : 1 ;", '1', '0'), '0');
  EXPECT_EQ(EdgeAgainstLevelRow("n ? : ? : 1 ;", '1', 'x'), '0');
}

TEST(MixedUdpEvaluation, LevelDominatesAnyChangeAbbreviation) {
  EXPECT_EQ(EdgeAgainstLevelRow("* ? : ? : 1 ;", '0', '1'), '0');
  EXPECT_EQ(EdgeAgainstLevelRow("* ? : ? : 1 ;", '1', '0'), '0');
}

TEST(MixedUdpEvaluation, EdgeAbbreviationDrivesOutputWithoutALevelMatch) {
  auto r = Parse(
      "primitive abbrev_only (q, clk, d);\n"
      "  output q; reg q;\n"
      "  input clk, d;\n"
      "  table\n"
      "    p ? : ? : 1 ;\n"
      "    ? 1 : ? : 0 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);
  UdpEvalState state(udp);
  state.SetOutput('0');
  state.SetInputs({'0', '0'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '0'}, 0, '0'), '1');
}

TEST(MixedUdpEvaluation, LevelRowNamingTheEdgeInputsNewValueDominates) {
  auto r = Parse(
      "primitive new_value_dom (q, clk, d);\n"
      "  output q; reg q;\n"
      "  input clk, d;\n"
      "  table\n"
      "    (01) 1 : ? : 1 ;\n"
      "    1    1 : ? : 0 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);
  UdpEvalState state(udp);
  state.SetOutput('1');
  state.SetInputs({'0', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'1', '1'}, 0, '0'), '0');
}

constexpr const char* kClauseJkEdgeFf =
    "primitive jk_edge_ff (q, clock, j, k, preset, clear);\n"
    "  output q; reg q;\n"
    "  input clock, j, k, preset, clear;\n"
    "  table\n"
    "    ?  ??  01  : ? : 1 ;\n"
    "    ?  ??  *1  : 1 : 1 ;\n"
    "    ?  ??  10  : ? : 0 ;\n"
    "    ?  ??  1*  : 0 : 0 ;\n"
    "    r  00  00  : 0 : 1 ;\n"
    "    r  00  11  : ? : - ;\n"
    "    r  01  11  : ? : 0 ;\n"
    "    r  10  11  : ? : 1 ;\n"
    "    r  11  11  : 0 : 1 ;\n"
    "    r  11  11  : 1 : 0 ;\n"
    "    f  ??  ??  : ? : - ;\n"
    "    b  *?  ??  : ? : - ;\n"
    "    b  ?*  ??  : ? : - ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(MixedUdpEvaluation, ClauseTablePresetDominatesFallingClockHold) {
  auto r = Parse(kClauseJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);
  UdpEvalState state(udp);
  state.SetOutput('0');
  state.SetInputs({'1', '0', '0', '0', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '0', '1'}, 0, '1'), '1');
}

TEST(MixedUdpEvaluation, ClauseTableFallingClockHoldsWithoutALevelMatch) {
  auto r = Parse(kClauseJkEdgeFf);
  ASSERT_NE(r.cu, nullptr);
  const UdpDecl& udp = ParseSingleUdp(r);
  UdpEvalState state(udp);
  state.SetOutput('0');
  state.SetInputs({'1', '0', '0', '1', '1'});
  EXPECT_EQ(state.EvaluateWithEdge({'0', '0', '0', '1', '1'}, 0, '1'), '0');
}

std::string RunSteps(const std::string& primitive, const char* declarations,
                     const char* instance,
                     const std::vector<const char*>& steps, const char* shown) {
  std::string body;
  for (const char* step : steps) {
    body += std::string("    #1 ") + step + "\n    #1 $write(\"%b\", " + shown +
            ");\n";
  }
  SimFixture f;
  std::string out = RunCapture(primitive + "module m;\n" + declarations +
                                   instance + "  initial begin\n" + body +
                                   "    $display;\n  end\nendmodule\n",
                               f);
  EXPECT_FALSE(f.has_errors);
  return out;
}

TEST(MixedUdpRun, LevelEntryDominatesARisingClockOnTheOutputNet) {
  EXPECT_EQ(RunSteps(kLvlDomEdgeFirst, "  reg clk, d;\n  wire q;\n",
                     "  lvl_dom u (q, clk, d);\n",
                     {"clk = 0; d = 0;", "clk = 1;", "clk = 0; d = 1;",
                      "clk = 1;", "d = 0;", "clk = 0;", "clk = 1;"},
                     "q"),
            "x100xx1\n");
}

TEST(MixedUdpRun, ClauseJkFlipFlopFollowsItsLevelAndEdgeEntries) {
  EXPECT_EQ(
      RunSteps(
          kClauseJkEdgeFf, "  reg clock, j, k, preset, clear;\n  wire q;\n",
          "  jk_edge_ff u (q, clock, j, k, preset, clear);\n",
          {"clock = 0; j = 0; k = 0; preset = 0; clear = 1;", "preset = 1;",
           "clear = 0;", "clear = 1;", "j = 1;", "clock = 1;", "clock = 0;",
           "k = 1;", "clock = 1;", "clock = 0;", "clock = 1;", "j = 0;",
           "clock = 0;", "clock = 1;", "k = 0;", "clock = 0;", "clock = 1;",
           "preset = 0;", "clock = 0;"},
          "q"),
      "1100011100111000011\n");
}

}  // namespace
