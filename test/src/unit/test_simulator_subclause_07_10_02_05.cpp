#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(QueuePopBackSim, ReturnsLastElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {10, 20, 30};\n"
      "  int result;\n"
      "  initial result = q.pop_back();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(QueuePopBackSim, ReturnsLastElementFourState) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] q[$] = {8'hAA, 8'h55};\n"
      "  int result;\n"
      "  initial result = q.pop_back();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x55u);
}

TEST(QueuePopBackSim, RemovesBackLeavingRestInOrder) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {10, 20, 30};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_back();\n"
      "    result = q[0] * 100 + q[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1020u);
}

TEST(QueuePopBackSim, ReducesSizeByOne) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {10, 20, 30};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_back();\n"
      "    result = q.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(QueuePopBackSim, RepeatedCallsDrainBackToFront) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {1, 2, 3};\n"
      "  int a, b, c, result;\n"
      "  initial begin\n"
      "    a = q.pop_back();\n"
      "    b = q.pop_back();\n"
      "    c = q.pop_back();\n"
      "    result = a * 100 + b * 10 + c;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 321u);
}

TEST(QueuePopBackSim, ResultUsableAsExpressionOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {5, 9};\n"
      "  int result;\n"
      "  initial result = q.pop_back() + 100;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 109u);
}

TEST(QueuePopBackSim, BackIsNewestPushBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(41);\n"
      "    q.push_back(42);\n"
      "    result = q.pop_back();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(QueuePopBackSim, BackOfProceduralAssignmentPattern) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q = {100, 200, 300};\n"
      "    result = q.pop_back();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 300u);
}

TEST(QueuePopBackSim, SingleElementLeavesQueueEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {42};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_back();\n"
      "    result = q.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(QueuePopBackSim, EmptyFourStateLogicQueueReturnsX) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] q[$];\n"
      "  int result;\n"
      "  initial result = $isunknown(q.pop_back());\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(QueuePopBackSim, EmptyTwoStateIntQueueReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial result = q.pop_back();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(QueuePopBackSim, EmptyTwoStateIntQueueHasNoUnknownBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial result = $isunknown(q.pop_back());\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(QueuePopBackSim, DrainedFourStateQueueThenPopReturnsX) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] q[$];\n"
      "  logic [7:0] last;\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(8'h55);\n"
      "    last = q.pop_back();\n"
      "    result = $isunknown(q.pop_back());\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(QueuePopBackSim, EmptyQueuePopLeavesQueueEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_back();\n"
      "    result = q.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(QueuePopBackSim, PopOnEmptyDoesNotDisturbLaterPush) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_back();\n"
      "    q.pop_back();\n"
      "    q.push_back(77);\n"
      "    result = q.size() * 1000 + q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1077u);
}

TEST(QueuePopBackSim, ReturnsSignedForASignedElementType) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  bit [31:0] u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    q.push_back(u);\n"
      "    result = q.pop_back() < 0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(QueuePopBackSim, ReturnsUnsignedForAnUnsignedElementType) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [31:0] q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(-5);\n"
      "    result = q.pop_back() < 0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

}  // namespace
