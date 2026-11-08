#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_queue.h"

using namespace delta;

namespace {

TEST(QueueMethods, InsertAtIndexFromSource) {
  RunAndExpectQueue(
      "module m;\n"
      "  int q [$] = '{10, 30};\n"
      "  initial q.insert(1, 20);\n"
      "endmodule\n",
      "q", {10u, 20u, 30u});
}

TEST(QueueMethods, InsertAtFrontFromSource) {
  RunAndExpectQueue(
      "module m;\n"
      "  int q [$] = '{20, 30};\n"
      "  initial q.insert(0, 10);\n"
      "endmodule\n",
      "q", {10u, 20u, 30u});
}

TEST(QueueMethods, InsertAtEndFromSource) {
  RunAndExpectQueue(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  initial q.insert(2, 30);\n"
      "endmodule\n",
      "q", {10u, 20u, 30u});
}

TEST(QueueMethods, InsertIntoEmptyQueueFromSource) {
  RunAndExpectQueue(
      "module m;\n"
      "  int q [$];\n"
      "  initial q.insert(0, 42);\n"
      "endmodule\n",
      "q", {42u});
}

TEST(QueueMethods, InsertOutOfRangeIsNoopFromSource) {
  RunAndExpectQueue(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  initial q.insert(100, 99);\n"
      "endmodule\n",
      "q", {10u, 20u});
}

TEST(QueueMethods, InsertJustPastEndIsNoopFromSource) {
  RunAndExpectQueue(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  initial q.insert(3, 99);\n"
      "endmodule\n",
      "q", {10u, 20u});
}

TEST(QueueMethods, InsertNegativeIndexIsNoopFromSource) {
  RunAndExpectQueue(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  integer idx = -1;\n"
      "  initial q.insert(idx, 99);\n"
      "endmodule\n",
      "q", {10u, 20u});
}

TEST(QueueMethods, InsertXzIndexIsNoopFromSource) {
  RunAndExpectQueue(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  integer idx = 'x;\n"
      "  initial q.insert(idx, 99);\n"
      "endmodule\n",
      "q", {10u, 20u});
}

TEST(QueueMethods, InsertOnVectorQueueFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$] = '{8'hAA, 8'hCC};\n"
      "  initial q.insert(1, 8'hBB);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0xAAu);
  EXPECT_EQ(q->elements[1].ToUint64(), 0xBBu);
  EXPECT_EQ(q->elements[2].ToUint64(), 0xCCu);
}

TEST(QueueMethods, InsertPreservesUnknownItemBitsFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$] = '{8'h11};\n"
      "  initial q.insert(0, 8'b1010_xxxx);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_FALSE(q->elements[0].IsKnown());
  EXPECT_TRUE(q->elements[1].IsKnown());
  EXPECT_EQ(q->elements[1].ToUint64(), 0x11u);
}

TEST(QueueMethods, InsertWithZIndexIsNoopFromSource) {
  RunAndExpectQueue(
      "module m;\n"
      "  int q [$] = '{10, 20};\n"
      "  integer idx = 'z;\n"
      "  initial q.insert(idx, 99);\n"
      "endmodule\n",
      "q", {10u, 20u});
}

TEST(QueueMethods, InsertsAnArrayElementIntoAQueueOfArrays) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int r[$][3];\n"
      "  int a[3] = '{1, 2, 3};\n"
      "  initial begin\n"
      "    r.push_back('{4, 5, 6});\n"
      "    r.push_back(a);\n"
      "    r.insert(1, '{7, 8, 9});\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", r.size(), r[0][2], r[1][0],\n"
      "             r[1][1], r[1][2], r[2][2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 6 7 8 9 3\n");
}

}  // namespace
