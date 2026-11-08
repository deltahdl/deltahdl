#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

constexpr const char* kLatch =
    "primitive latch (q, ena_, data);\n"
    "  output q; reg q;\n"
    "  input ena_, data;\n"
    "  table\n"
    "  // ena_ data : q : q+\n"
    "    0 1 : ? : 1 ;\n"
    "    0 0 : ? : 0 ;\n"
    "    1 ? : ? : - ;  // - = no change\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpLevelSeq, RegOutputHoldsStateAndTracksIt) {
  auto r = Parse(kLatch);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), 'x');

  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');

  EXPECT_EQ(state.Evaluate({'1', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '0');
  EXPECT_EQ(state.GetOutput(), '0');

  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpLevelSeq, OutputFieldIsNextState) {
  auto r = Parse(kLatch);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
}

TEST(UdpLevelSeq, NoChangeOutputSymbolHoldsCurrentState) {
  auto r = Parse(kLatch);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'1', '0'}), '1');
}

constexpr const char* kStateKeyed =
    "primitive cs (q, s);\n"
    "  output q; reg q;\n"
    "  input s;\n"
    "  table\n"
    "  // s : q : q+\n"
    "    1 : ? : 0 ;\n"
    "    0 : 0 : 1 ;\n"
    "    0 : 1 : - ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpLevelSeq, CurrentStateFieldSelectsRow) {
  auto r = Parse(kStateKeyed);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'1'}), '0');
  EXPECT_EQ(state.Evaluate({'0'}), '1');
  EXPECT_EQ(state.Evaluate({'0'}), '1');
  EXPECT_EQ(state.Evaluate({'0'}), '1');
  EXPECT_EQ(state.Evaluate({'1'}), '0');
  EXPECT_EQ(state.Evaluate({'0'}), '1');
}

constexpr const char* kBStateKeyed =
    "primitive bcs (q, s);\n"
    "  output q; reg q;\n"
    "  input s;\n"
    "  table\n"
    "  // s : q : q+\n"
    "    0 : b : 1 ;\n"
    "    1 : ? : 0 ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpLevelSeq, CurrentStateFieldBMatchesZeroAndOneNotX) {
  auto r = Parse(kBStateKeyed);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), 'x');
  EXPECT_EQ(state.Evaluate({'0'}), 'x');
  EXPECT_EQ(state.Evaluate({'1'}), '0');
  EXPECT_EQ(state.Evaluate({'0'}), '1');
  EXPECT_EQ(state.Evaluate({'0'}), '1');
}

}  // namespace
