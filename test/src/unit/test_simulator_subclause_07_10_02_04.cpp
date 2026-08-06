// Tests for §7.10.2.4 "pop_front()".
//
// pop_front() removes and returns the first element of a queue. Its normative
// content is entirely a simulator-stage concern, and its behavior depends on
// how the queue is produced - its declared element type, how it was
// initialized, and whether it is currently empty. These tests therefore build
// each queue from real SystemVerilog source and drive it through the full
// pipeline (parse, elaborate, lower, run), observing the result through an
// ordinary int variable rather than hand-building queue state.
//
//   C1 - pop_front() removes and returns the element at the front (position 0).
//   C2 - On an empty queue the return value is the value of a nonexistent
//        element of the queue's element type, per Table 7-1 (see 7.4.5, a
//        dependency): all-x for a 4-state element type, all-zero for a 2-state
//        element type.
//   C3 - On an empty queue the call has no effect: the queue stays empty.
//
// Production rule: src/simulator/eval_array_queue.cpp (PopQueueFront /
// NonexistentQueueElement). The nonexistent-element value it returns is the
// §7.4.5 machinery this pass depends on.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- C1: removes and returns the first element ------------------------------

// Declaration-initializer form: the queue is built by an assignment-pattern
// initializer, and pop_front() as an assignment RHS yields the front element.
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

// After the call the removed element is the former front: the new front is the
// element that was at position 1.
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

// A pop_front() removes exactly one element: size drops by one.
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

// Successive pop_front() calls drain the queue strictly front-to-back.
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

// The returned value is usable directly as an operand in a larger expression.
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

// A queue built procedurally via push_back (not a declaration initializer)
// pops the element that was pushed first.
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

// A queue populated by a procedural assignment-pattern statement (not a
// declaration initializer, and a different runtime path) still pops the
// element written at the front of the pattern.
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

// Popping the sole element returns it and leaves the queue empty.
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

// --- C2: empty queue returns the Table 7-1 nonexistent-element value --------

// A 4-state element type (logic vector): popping an empty queue yields an
// all-x value, observed here through $isunknown.
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

// A 2-state element type (int): the nonexistent element is all-zero, not x.
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

// And that 2-state empty result carries no unknown bits.
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

// Draining a 4-state queue to empty and popping again yields the nonexistent
// value: the transition into the empty state is what triggers the rule.
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

// --- C3: empty queue is left unchanged --------------------------------------

// Popping an empty queue has no effect: it stays empty (size still 0).
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

// A queue drained to empty, then popped again, remains empty; a subsequent
// push_back still lands normally, proving the empty pop did not corrupt state.
TEST(QueuePopFrontSim, PopOnEmptyDoesNotDisturbLaterPush) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_front();\n"    // now empty
      "    q.pop_front();\n"    // no effect
      "    q.push_back(77);\n"  // still usable
      "    result = q.size() * 1000 + q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1077u);  // size 1, front is 77
}

}  // namespace
