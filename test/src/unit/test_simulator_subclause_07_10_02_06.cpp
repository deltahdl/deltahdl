#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(QueuePushFrontSim, ShiftsExistingElementsUp) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {20, 30};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_front(10);\n"
      "    result = q[0] * 10000 + q[1] * 100 + q[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 102030u);
}

TEST(QueuePushFrontSim, IncreasesSizeByOne) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {20, 30};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_front(10);\n"
      "    result = q.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(QueuePushFrontSim, OnEmptyQueueBecomesSoleElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_front(42);\n"
      "    result = q.size() * 1000 + q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1042u);
}

TEST(QueuePushFrontSim, MultiplePushesAccumulateAtFront) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_front(1);\n"
      "    q.push_front(2);\n"
      "    q.push_front(3);\n"
      "    result = q[0] * 100 + q[1] * 10 + q[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 321u);
}

TEST(QueuePushFrontSim, InterleavedWithPushBackOrdersFrontVsBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(2);\n"
      "    q.push_front(1);\n"
      "    q.push_back(3);\n"
      "    result = q[0] * 100 + q[1] * 10 + q[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 123u);
}

TEST(QueuePushFrontSim, InsertsFourStateElementAtFront) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] q[$] = {8'h55};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_front(8'hAA);\n"
      "    result = q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xAAu);
}

TEST(QueuePushFrontSim, ItemFromRuntimeExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {20};\n"
      "  int x = 3;\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_front(x + 4);\n"
      "    result = q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(QueuePushFrontSim, OnProceduralAssignmentPatternQueue) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q = {100, 200};\n"
      "    q.push_front(50);\n"
      "    result = q[0] * 100 + q[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5100u);
}

TEST(QueuePushFrontSim, PushedValueRoundTripsThroughPopFront) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {20};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_front(9);\n"
      "    result = q.pop_front();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(QueuePushFrontSim, PushesAnArrayVariableOntoAQueueOfArrays) {
  auto v = RunAndGet(
      "module t;\n"
      "  int r[$][3];\n"
      "  int a[3] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    r.push_back('{4, 5, 6});\n"
      "    r.push_front(a);\n"
      "    result = r[0][0] * 1000 + r[0][1] * 100 + r[0][2] * 10 + r[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1236u);
}

}  // namespace
