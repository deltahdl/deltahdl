// Tests for §7.10.2.6 "push_front()".
//
// push_front() inserts the given element at the front (position 0) of a queue,
// shifting the existing elements up by one. Its prototype is
// `function void push_front(input element_t item)`: it returns nothing and
// takes a single element_t argument. The normative content is entirely a
// simulator-stage concern, and its behavior depends on how the queue is
// produced - its declared element type and how it was initialized - and on how
// the pushed item is produced. These tests therefore build each queue and each
// item from real SystemVerilog source and drive them through the full pipeline
// (parse, elaborate, lower, run), observing the result through ordinary
// variables rather than hand-building queue state.
//
//   C1 - push_front(item) places item at the front (position 0); every element
//        already in the queue moves up one position, and the size grows by one.
//
// There is no empty-queue special case (push_front always inserts) and no
// reject path in §7.10.2.6, so - like the pop_front/pop_back siblings
// (§7.10.2.4/§7.10.2.5) - there is no negative test. push_front is the
// front-insertion mirror of push_back (§7.10.2.7). The queue declaration
// (§7.10) and the assignment-pattern initializers (§10.9/§10.10) are the
// dependency syntax the inputs are built from.
//
// Production rule: src/simulator/eval_array_queue.cpp (QueuePushFront,
// dispatched through DispatchQueuePush).

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- C1: inserts the item at the front --------------------------------------

// Declaration-initializer form: the queue is built by an assignment-pattern
// initializer, and after push_front the pushed element is the new front while
// the elements already present move up by one position: {20, 30} with 10 pushed
// to the front becomes {10, 20, 30}, read back in order.
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
  EXPECT_EQ(v, 102030u);  // queue is {10, 20, 30}
}

// push_front adds exactly one element: size grows by one.
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

// On an empty queue push_front makes the item the sole (front) element.
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
  EXPECT_EQ(v, 1042u);  // size 1, front is 42
}

// Successive push_front calls stack up at the front, so the queue ends up in
// the reverse of the push order: pushing 1, then 2, then 3 yields {3, 2, 1}.
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
  EXPECT_EQ(v, 321u);  // queue is {3, 2, 1}
}

// push_front and push_back insert at opposite ends: interleaving them shows the
// front vs. back distinction. push_back(2), push_front(1), push_back(3) yields
// {1, 2, 3}.
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
  EXPECT_EQ(v, 123u);  // queue is {1, 2, 3}
}

// A 4-state logic-vector element type: the wide element is inserted at the
// front with its full value, exercising a different element-storage path than
// int.
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

// The item argument is not required to be a literal or a constant: it can be a
// runtime expression built from a variable, which is evaluated and the
// resulting value placed at the front.
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

// A queue populated by a procedural assignment-pattern statement (a different
// runtime path than a declaration initializer) still takes the pushed element
// at its front, ahead of the pattern's elements.
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
  EXPECT_EQ(v, 5100u);  // queue is {50, 100, 200}
}

// The element placed at the front by push_front is exactly what pop_front
// (§7.10.2.4) removes and returns next: the two are inverse front operations.
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

}  // namespace
