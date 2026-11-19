#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "fixture_simulator.h"
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

constexpr const char* kXStateKeyed =
    "primitive xcs (q, e, d);\n"
    "  output q; reg q;\n"
    "  input e, d;\n"
    "  table\n"
    "  // e d : q : q+\n"
    "    1 0 : ? : 0 ;\n"
    "    1 1 : ? : 1 ;\n"
    "    0 ? : x : 1 ;\n"
    "    0 ? : 1 : 0 ;\n"
    "    0 ? : 0 : - ;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpLevelSeq, ExplicitXCurrentStateMatchesOnlyAHeldX) {
  auto r = Parse(kXStateKeyed);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), 'x');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '0');
  EXPECT_EQ(state.Evaluate({'1', '1'}), '1');
  EXPECT_EQ(state.Evaluate({'0', '0'}), '0');
  EXPECT_EQ(state.Evaluate({'1', 'x'}), 'x');
  EXPECT_EQ(state.Evaluate({'0', '1'}), '1');
}

std::string RunLatchInstances(const std::string& definition) {
  SimFixture f;
  std::string out = RunCapture(definition +
                                   "module m;\n"
                                   "  reg ena_, data;\n"
                                   "  wire q, gq;\n"
                                   "  latch u(q, ena_, data);\n"
                                   "  if (1) begin : g\n"
                                   "    latch v(gq, ena_, data);\n"
                                   "  end\n"
                                   "  task show; $write(\"%b%b \", q, gq); "
                                   "endtask\n"
                                   "  initial begin\n"
                                   "    #1 show;\n"
                                   "    ena_ = 0; data = 1; #1 show;\n"
                                   "    ena_ = 1; #1 data = 0; #1 show;\n"
                                   "    ena_ = 0; #1 show;\n"
                                   "    ena_ = 1; #1 data = 1; #1 show;\n"
                                   "    $display;\n"
                                   "  end\n"
                                   "endmodule\n",
                               f);
  EXPECT_FALSE(f.has_errors);
  return out;
}

constexpr const char* kLatchOutput = "xx 11 11 00 00 \n";

TEST(UdpLevelSeqRun, LatchInstanceOutputFollowsItsInternalState) {
  EXPECT_EQ(RunLatchInstances(kLatch), kLatchOutput);
}

TEST(UdpLevelSeqRun, LatchWithAnsiRegOutputFollowsItsInternalState) {
  EXPECT_EQ(RunLatchInstances("primitive latch (output reg q, input ena_, "
                              "data);\n"
                              "  table\n"
                              "    0 1 : ? : 1 ;\n"
                              "    0 0 : ? : 0 ;\n"
                              "    1 ? : ? : - ;\n"
                              "  endtable\n"
                              "endprimitive\n"),
            kLatchOutput);
}

}  // namespace
