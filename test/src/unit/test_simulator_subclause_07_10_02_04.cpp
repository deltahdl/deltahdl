#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(QueuePopFrontSim, ReturnsFirstElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {10, 20, 30};\n"
      "  int result;\n"
      "  initial result = q.pop_front();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

TEST(QueuePopFrontSim, RemovesFrontLeavingRestInOrder) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {10, 20, 30};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_front();\n"
      "    result = q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(QueuePopFrontSim, ReducesSizeByOne) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {10, 20, 30};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_front();\n"
      "    result = q.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(QueuePopFrontSim, RepeatedCallsDrainFrontToBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {1, 2, 3};\n"
      "  int a, b, c, result;\n"
      "  initial begin\n"
      "    a = q.pop_front();\n"
      "    b = q.pop_front();\n"
      "    c = q.pop_front();\n"
      "    result = a * 100 + b * 10 + c;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 123u);
}

TEST(QueuePopFrontSim, ResultUsableAsExpressionOperand) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {5, 9};\n"
      "  int result;\n"
      "  initial result = q.pop_front() + 100;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 105u);
}

TEST(QueuePopFrontSim, FrontIsOldestPushBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(41);\n"
      "    q.push_back(42);\n"
      "    result = q.pop_front();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 41u);
}

TEST(QueuePopFrontSim, FrontOfProceduralAssignmentPattern) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q = {100, 200, 300};\n"
      "    result = q.pop_front();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 100u);
}

TEST(QueuePopFrontSim, SingleElementLeavesQueueEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {42};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_front();\n"
      "    result = q.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(QueuePopFrontSim, EmptyFourStateLogicQueueReturnsX) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] q[$];\n"
      "  int result;\n"
      "  initial result = $isunknown(q.pop_front());\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(QueuePopFrontSim, EmptyTwoStateIntQueueReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial result = q.pop_front();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(QueuePopFrontSim, EmptyTwoStateIntQueueHasNoUnknownBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial result = $isunknown(q.pop_front());\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(QueuePopFrontSim, DrainedFourStateQueueThenPopReturnsX) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] q[$];\n"
      "  logic [7:0] first;\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(8'h55);\n"
      "    first = q.pop_front();\n"
      "    result = $isunknown(q.pop_front());\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(QueuePopFrontSim, EmptyQueuePopLeavesQueueEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_front();\n"
      "    result = q.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(QueuePopFrontSim, PopOnEmptyDoesNotDisturbLaterPush) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_front();\n"
      "    q.pop_front();\n"
      "    q.push_back(77);\n"
      "    result = q.size() * 1000 + q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1077u);
}

TEST(QueuePopFrontSim, ReturnsSignedForASignedElementType) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  bit [31:0] u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    q.push_back(u);\n"
      "    result = q.pop_front() < 0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(QueuePopFrontSim, ReturnsUnsignedForAnUnsignedElementType) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [31:0] q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(-5);\n"
      "    result = q.pop_front() < 0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

}  // namespace
