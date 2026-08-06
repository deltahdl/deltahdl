// Tests for §7.10.2.7 "push_back()".
//
// push_back() inserts the given element at the end (last position) of a queue,
// leaving the elements already present in place. Its prototype is
// `function void push_back(input element_t item)`: it returns nothing and takes
// a single element_t argument. The normative content is entirely a
// simulator-stage concern, and its behavior depends on how the queue is
// produced - its declared element type and how it was initialized - and on how
// the pushed item is produced. These tests therefore build each queue and each
// item from real SystemVerilog source and drive them through the full pipeline
// (parse, elaborate, lower, run), observing the result through ordinary
// variables rather than hand-building queue state.
//
//   C1 - push_back(item) places item at the end (last position); the elements
//        already in the queue keep their positions, and the size grows by one.
//
// There is no empty-queue special case (push_back always inserts) and no reject
// path in §7.10.2.7, so - like the pop_front/pop_back siblings
// (§7.10.2.4/§7.10.2.5) - there is no negative test. push_back is the
// end-insertion mirror of push_front (§7.10.2.6). The queue declaration (§7.10)
// and the assignment-pattern initializers (§10.9/§10.10) are the dependency
// syntax the inputs are built from.
//
// Production rule: src/simulator/eval_array_queue.cpp (QueuePushBack,
// dispatched through DispatchQueuePush).

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- C1: appends the item at the end ----------------------------------------

// Declaration-initializer form: the queue is built by an assignment-pattern
// initializer, and after push_back the pushed element is the new last element
// while the elements already present keep their positions: {10, 20} with 30
// pushed to the back becomes {10, 20, 30}, read back in order.
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
  EXPECT_EQ(v, 102030u);  // queue is {10, 20, 30}
}

// push_back adds exactly one element: size grows by one.
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

// On an empty queue push_back makes the item the sole (last) element.
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
  EXPECT_EQ(v, 1042u);  // size 1, sole element is 42
}

// Successive push_back calls append at the end, so the queue ends up in the
// same order as the push order: pushing 1, then 2, then 3 yields {1, 2, 3}.
// (Contrast push_front, which reverses to {3, 2, 1}.)
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
  EXPECT_EQ(v, 123u);  // queue is {1, 2, 3}
}

// push_back and push_front insert at opposite ends: interleaving them shows the
// back vs. front distinction. push_back(1), push_back(2), push_back(3) builds
// {1, 2, 3}, then push_front(9) prepends to give {9, 1, 2, 3}.
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
  EXPECT_EQ(v, 9123u);  // queue is {9, 1, 2, 3}
}

// A 4-state logic-vector element type: the wide element is appended at the end
// with its full value, exercising a different element-storage path than int.
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
  EXPECT_EQ(v, 0xAAu);  // appended element is the new last element (index 1)
}

// A string element type: element_t admits any legal type, so a queue of strings
// takes the pushed string at its end through a distinct (non-integral) storage
// path. The appended string becomes the new last element.
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
  EXPECT_EQ(v, 7u);  // {"a", "bee"}: pushed string is the new last element
}

// A real element type exercises the floating-point storage path: the pushed
// real value is appended at the end and read back unchanged.
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
  EXPECT_EQ(v, 9u);  // {1.5, 2.5}: pushed real is the new last element
}

// The item argument is not required to be a literal or a constant: it can be a
// runtime expression built from a variable, which is evaluated and the
// resulting value placed at the end.
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
  EXPECT_EQ(v, 7u);  // appended at the end, index 1
}

// A queue populated by a procedural assignment-pattern statement (a different
// runtime path than a declaration initializer) still takes the pushed element
// at its end, after the pattern's elements.
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
  EXPECT_EQ(v, 20050u);  // queue is {100, 200, 50}
}

// The element appended at the end by push_back is exactly what pop_back
// (§7.10.2.5) removes and returns next: the two are inverse back operations.
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

}  // namespace
