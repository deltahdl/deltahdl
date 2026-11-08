#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
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

}  // namespace
