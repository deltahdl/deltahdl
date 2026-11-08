#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(QueuePushBackSim, AppendsElementAtEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {10, 20};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(30);\n"
      "    result = q[0] * 10000 + q[1] * 100 + q[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 102030u);
}

TEST(QueuePushBackSim, IncreasesSizeByOne) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {20, 30};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    result = q.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(QueuePushBackSim, OnEmptyQueueBecomesSoleElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(42);\n"
      "    result = q.size() * 1000 + q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1042u);
}

TEST(QueuePushBackSim, MultiplePushesAccumulateAtEndInOrder) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(2);\n"
      "    q.push_back(3);\n"
      "    result = q[0] * 100 + q[1] * 10 + q[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 123u);
}

TEST(QueuePushBackSim, InterleavedWithPushFrontOrdersBackVsFront) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(1);\n"
      "    q.push_back(2);\n"
      "    q.push_back(3);\n"
      "    q.push_front(9);\n"
      "    result = q[0] * 1000 + q[1] * 100 + q[2] * 10 + q[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9123u);
}

TEST(QueuePushBackSim, AppendsFourStateElementAtEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] q[$] = {8'h55};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(8'hAA);\n"
      "    result = q[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xAAu);
}

TEST(QueuePushBackSim, AppendsStringElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  string q[$] = {\"a\"};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(\"bee\");\n"
      "    result = (q[0] == \"a\" && q[1] == \"bee\") ? 7 : 0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(QueuePushBackSim, AppendsRealElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  real q[$] = {1.5};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(2.5);\n"
      "    result = (q[0] == 1.5 && q[1] == 2.5) ? 9 : 0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(QueuePushBackSim, ItemFromRuntimeExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {20};\n"
      "  int x = 3;\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(x + 4);\n"
      "    result = q[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(QueuePushBackSim, OnProceduralAssignmentPatternQueue) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q = {100, 200};\n"
      "    q.push_back(50);\n"
      "    result = q[1] * 100 + q[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20050u);
}

TEST(QueuePushBackSim, PushedValueRoundTripsThroughPopBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {20};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(9);\n"
      "    result = q.pop_back();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(QueuePushBackSim, ElementKeepsTheValueOfAStructPushed) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int a; int b; } s_t;\n"
      "  s_t q[$];\n"
      "  s_t e;\n"
      "  int result;\n"
      "  initial begin\n"
      "    e.a = 11; e.b = 22;\n"
      "    q.push_back(e);\n"
      "    e.a = 3;\n"
      "    q.insert(0, e);\n"
      "    e.a = 0;\n"
      "    result = q[1].a * 10000 + q[0].a * 100 + q[1].b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 110322u);
}

TEST(QueuePushBackSim, PushesAnArrayVariableOntoAQueueOfArrays) {
  auto v = RunAndGet(
      "module t;\n"
      "  int r[$][3];\n"
      "  int a[3] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    r.push_back('{4, 5, 6});\n"
      "    r.push_back(a);\n"
      "    a[1] = 9;\n"
      "    result = r.size() * 10000 + r[1][0] * 100 + r[1][1] * 10 +\n"
      "             r[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20123u);
}

}  // namespace
