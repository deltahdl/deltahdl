#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueueDelete, DeleteFirstElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 0)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueDelete, DeleteLastElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 2)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueDelete, DeleteOnlyElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {42});
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 0)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueDelete, NoArgOnEmptyQueueIsNoop) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  auto* call = MakeMethodCall(f.arena, "q", "delete", {});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueDelete, DeleteOnEmptyQueueWithIndexIsNoop) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  auto* call = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 0)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

// The tests above stub the queue with a helper and call the exec entry point
// directly. §7.10.2.3's rules operate on a queue whose contents come from a
// declaration + initializer (§7.10) and on an index taken from a variable of
// the prototype's `integer` formal, so the behavior depends on how those
// inputs are produced. The tests below build both from real source and drive
// them through the full pipeline (parse, elaborate, lower, run), observing the
// production delete() path (DispatchQueueDelete reached via
// TryEvalQueueMethodCall) apply each rule.

// Claim: delete(index) removes the element at that ordinal position, leaving
// the surrounding elements in order.
TEST(QueueDelete, DeleteAtIndexFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20, 30};\n"
      "  initial q.delete(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

// Claim: with no index argument, delete() removes every element, leaving the
// queue empty.
TEST(QueueDelete, NoArgClearsAllFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20, 30};\n"
      "  initial q.delete();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

// Claim: the property-style call `q.delete;` (no parentheses) is the no-index
// form and clears the queue.
TEST(QueueDelete, PropertyStyleClearsAllFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{1, 2, 3, 4};\n"
      "  initial q.delete;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

// Claim (error path): an index greater than or equal to the current size leaves
// the queue unchanged.
TEST(QueueDelete, IndexOutOfRangeIsNoopFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20, 30};\n"
      "  initial q.delete(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

// Claim (error path): the boundary case where the index equals the current
// size is out of range (valid indices are 0..size-1) and leaves the queue
// unchanged. This exercises the exact off-by-one edge of the range guard on the
// real pipeline, complementing the strictly-greater case above.
TEST(QueueDelete, IndexEqualToSizeIsNoopFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20, 30};\n"
      "  initial q.delete(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

// Claim (error path): a negative index leaves the queue unchanged. The index is
// held in an `integer` variable, matching the prototype's signed 4-state
// formal.
TEST(QueueDelete, NegativeIndexIsNoopFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20, 30};\n"
      "  integer idx = -1;\n"
      "  initial q.delete(idx);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

// Claim (error path): an index carrying x/z bits leaves the queue unchanged.
// `integer` is 4-state, so an unknown value survives to the delete() call.
TEST(QueueDelete, XzIndexIsNoopFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20, 30};\n"
      "  integer idx = 'x;\n"
      "  initial q.delete(idx);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 3u);
}

// Element-type input form: delete() is defined for a queue of any element type,
// not just int. Erase at an index on a queue of packed 4-state vectors and
// confirm the surrounding vector elements survive in order.
TEST(QueueDelete, DeleteAtIndexOnVectorQueueFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  initial q.delete(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0xAAu);
  EXPECT_EQ(q->elements[1].ToUint64(), 0xCCu);
}

// Element-type input form: the no-index clear form is likewise element-type
// agnostic. Empty a queue of signed bytes and confirm it drains to zero.
TEST(QueueDelete, ClearAllOnByteQueueFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte q [$] = '{1, 2, 3};\n"
      "  initial q.delete();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

// Error-path input form driven from real source: an index equal to the size of
// an empty queue (0 on an empty queue) is out of range, so delete(index) leaves
// the queue empty. The empty queue is produced by an initializer-less §7.10
// declaration rather than a stubbed helper.
TEST(QueueDelete, DeleteIndexOnEmptyQueueFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$];\n"
      "  initial q.delete(0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

// Index-operand input form: the index need not be a literal. A localparam read
// supplies the position, taking the parameter-resolution path rather than a
// literal-constant path, and the element at that position is removed.
TEST(QueueDelete, DeleteAtLocalparamIndexFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int P = 1;\n"
      "  int q [$] = '{10, 20, 30};\n"
      "  initial q.delete(P);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

// Dependency §7.10 supplies two initializer forms for a queue: the assignment
// pattern '{...} used above and the unpacked array concatenation {...}, which
// lowers by a different path. Drive delete(index) end to end over a queue built
// with the concatenation form to confirm the rule applies regardless of how the
// queue was populated.
TEST(QueueDelete, DeleteAtIndexOnConcatInitializedQueueFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = {10, 20, 30};\n"
      "  initial q.delete(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

}  // namespace
