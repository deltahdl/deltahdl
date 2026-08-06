// Tests for §7.10.2.5 "pop_back()".
//
// pop_back() removes and returns the last element of a queue. Its normative
// content is entirely a simulator-stage concern, and its behavior depends on
// how the queue is produced - its declared element type, how it was
// initialized, and whether it is currently empty. These tests therefore build
// each queue from real SystemVerilog source and drive it through the full
// pipeline (parse, elaborate, lower, run), observing the result through an
// ordinary int variable rather than hand-building queue state.
//
//   C1 - pop_back() removes and returns the element at the back (last
//   position). C2 - On an empty queue the return value is the value of a
//   nonexistent
//        element of the queue's element type, per Table 7-1 (see 7.4.5, a
//        dependency): all-x for a 4-state element type, all-zero for a 2-state
//        element type.
//   C3 - On an empty queue the call has no effect: the queue stays empty.
//
// Production rule: src/simulator/eval_array_queue.cpp (PopQueueBack /
// NonexistentQueueElement). The nonexistent-element value it returns is the
// §7.4.5 machinery this pass depends on. pop_back is the exact tail-end mirror
// of pop_front (§7.10.2.4): same empty-queue rule, opposite removal end.

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- C1: removes and returns the last element -------------------------------

// Declaration-initializer form: the queue is built by an assignment-pattern
// initializer, and pop_back() as an assignment RHS yields the last element.
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

// The removed/returned element carries the queue's declared element type. With
// a 4-state logic vector element type the popped last element is returned with
// its full value, exercising the return-copy path for a wide 4-state element
// rather than the 2-state int used elsewhere.
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

// After the call the removed element is the former back: the queue that was
// {10, 20, 30} is left as {10, 20}, with earlier positions unchanged.
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
  EXPECT_EQ(v, 1020u);  // remaining queue is {10, 20}
}

// A pop_back() removes exactly one element: size drops by one.
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

// Successive pop_back() calls drain the queue strictly back-to-front.
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

// The returned value is usable directly as an operand in a larger expression.
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

// A queue built procedurally via push_back (not a declaration initializer)
// pops the element that was pushed last.
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

// A queue populated by a procedural assignment-pattern statement (not a
// declaration initializer, and a different runtime path) still pops the
// element written at the back of the pattern.
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

// Popping the sole element returns it and leaves the queue empty.
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

// --- C2: empty queue returns the Table 7-1 nonexistent-element value --------

// A 4-state element type (logic vector): popping an empty queue yields an
// all-x value, observed here through $isunknown.
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

// A 2-state element type (int): the nonexistent element is all-zero, not x.
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

// And that 2-state empty result carries no unknown bits.
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

// Draining a 4-state queue to empty and popping again yields the nonexistent
// value: the transition into the empty state is what triggers the rule.
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

// --- C3: empty queue is left unchanged --------------------------------------

// Popping an empty queue has no effect: it stays empty (size still 0).
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

// A queue drained to empty, then popped again, remains empty; a subsequent
// push_back still lands normally, proving the empty pop did not corrupt state.
TEST(QueuePopBackSim, PopOnEmptyDoesNotDisturbLaterPush) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$] = {3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.pop_back();\n"     // now empty
      "    q.pop_back();\n"     // no effect
      "    q.push_back(77);\n"  // still usable
      "    result = q.size() * 1000 + q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1077u);  // size 1, back is 77
}

}  // namespace
