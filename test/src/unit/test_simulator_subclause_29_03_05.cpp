#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

TEST(UdpInputZAsX, CombinationalZMatchesXRow) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'z', '0'}), '1');
}

TEST(UdpInputZAsX, CombinationalBRowRejectsCoercedZ) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    b 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.Evaluate({'z', '1'}), 'x');
}

TEST(UdpInputZAsX, SequentialEdgeZTreatedAsX) {
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    p ? : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), '0');
  state.SetInputs({'0', '0'});
  state.EvaluateWithEdge({'z', '0'}, 0, '0');
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpInputZAsX, SequentialPreviousZTreatedAsX) {
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  initial q = 1;\n"
      "  table\n"
      "    n ? : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);

  UdpEvalState state(*r.cu->udps[0]);
  EXPECT_EQ(state.GetOutput(), '1');
  state.SetInputs({'z', '1'});
  state.EvaluateWithEdge({'0', '1'}, 0, 'z');
  EXPECT_EQ(state.GetOutput(), '0');
}

}  // namespace
