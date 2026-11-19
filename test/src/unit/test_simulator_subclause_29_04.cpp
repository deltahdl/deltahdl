#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_parser.h"
#include "fixture_simulator.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

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

TEST(UdpCombinational, SpecifiedRowDrivesTabledOutput) {
  auto r = Parse(kMultiplexer);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '1', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1', 'x'}), '1');
}

TEST(UdpCombinational, UnspecifiedCombinationDrivesX) {
  auto r = Parse(kMultiplexer);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'0', 'x', 'x'}), 'x');
  EXPECT_EQ(state.Evaluate({'x', 'x', 'x'}), 'x');
  EXPECT_EQ(state.Evaluate({'x', '0', '1'}), 'x');
}

TEST(UdpCombinational, OutputHasNoMemoryBetweenEvaluations) {
  auto r = Parse(kMultiplexer);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', 'x', 'x'}), 'x');
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
}

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
  EXPECT_EQ(state.Evaluate({'0', '1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '1', 'x'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', 'x', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', 'x', '0'}), 'x');
}

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
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'x', '1'}), 'x');
  EXPECT_EQ(state.Evaluate({'x', '0'}), 'x');
}

std::string RunMultiplexerThrough(const char* definition,
                                  const std::string& steps) {
  SimFixture f;
  std::string out =
      RunCapture(std::string(definition) +
                     "module m;\n"
                     "  reg c, a, b;\n"
                     "  wire y, gy;\n"
                     "  multiplexer u(y, c, a, b);\n"
                     "  if (1) begin : g\n"
                     "    multiplexer v(gy, c, a, b);\n"
                     "  end\n"
                     "  task show; $write(\"%b%b \", y, gy); endtask\n"
                     "  initial begin\n" +
                     steps +
                     "    $display;\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_FALSE(f.has_errors);
  return out;
}

constexpr const char* kXInputSteps =
    "    c = 0; a = 0; b = 0; #1 show;\n"
    "    a = 1; b = 1'bx; #1 show;\n"
    "    a = 0; b = 0; #1 show;\n"
    "    c = 1'bx; a = 1; b = 1; #1 show;\n"
    "    c = 0; a = 0; b = 0; #1 show;\n"
    "    c = 1; a = 1'bx; b = 1; #1 show;\n";

constexpr const char* kXInputOutput = "00 11 00 11 00 11 \n";

TEST(UdpCombinationalRun, XInputsSelectTheirRowsInTheFullMultiplexer) {
  EXPECT_EQ(RunMultiplexerThrough(kMultiplexer, kXInputSteps), kXInputOutput);
}

TEST(UdpCombinationalRun, XInputsSelectTheirRowsInTheAbbreviatedMultiplexer) {
  EXPECT_EQ(RunMultiplexerThrough(kMultiplexerAbbreviated, kXInputSteps),
            kXInputOutput);
}

constexpr const char* kUnlistedSteps =
    "    c = 0; a = 1; b = 0; #1 show;\n"
    "    a = 1'bx; b = 1'bx; #1 show;\n"
    "    a = 1; b = 0; #1 show;\n"
    "    a = 0; #1 show;\n"
    "    a = 1'bx; b = 1'bx; #1 show;\n"
    "    a = 0; b = 0; #1 show;\n";

constexpr const char* kUnlistedOutput = "11 xx 11 00 xx 00 \n";

TEST(UdpCombinationalRun,
     AnUnlistedCombinationDrivesXAndALaterListedOneLeavesIt) {
  EXPECT_EQ(RunMultiplexerThrough(kMultiplexer, kUnlistedSteps),
            kUnlistedOutput);
}

TEST(
    UdpCombinationalRun,
    AnUnlistedCombinationOfTheAbbreviatedTableDrivesXAndALaterListedOneLeavesIt) {
  EXPECT_EQ(RunMultiplexerThrough(kMultiplexerAbbreviated, kUnlistedSteps),
            kUnlistedOutput);
}

}  // namespace
