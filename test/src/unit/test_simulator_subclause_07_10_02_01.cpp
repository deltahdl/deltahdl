#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(QueueSizeSimulation, ReturnsThirtyTwoBitInt) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "size", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 32u);
}

TEST(QueueSizeSimulation, PropertyAccessReturnsZeroForEmpty) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  Logic4Vec out{};
  bool ok = TryEvalQueueProperty("q", "size", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(QueueSizeSimulation, QueueSizeNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    q.push_back(8'h01);\n"
      "    q.push_back(8'h02);\n"
      "    q.push_back(8'h03);\n"
      "    s = q.size;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 3u);
}

TEST(QueueSizeSimulation, SizeInForLoopCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20, 30};\n"
      "  int total;\n"
      "  initial begin\n"
      "    total = 0;\n"
      "    for (int j = 0; j < q.size; j++)\n"
      "      total = total + q[j];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("total")->value.ToUint64(), 60u);
}

// 7.10 allows a queue to be built from an unpacked array concatenation {a,b,c}
// as well as from an assignment pattern '{a,b,c}; the two initializers take
// different lowering paths. Confirm size() reports the element count of a queue
// produced by the concatenation form, driven end to end from real source.
TEST(QueueSizeSimulation, SizeCountsConcatenationInitializedQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = {5, 15, 25, 35};\n"
      "  int sz;\n"
      "  initial sz = q.size();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sz")->value.ToUint64(), 4u);
}

// A queue declared without an initializer starts empty (7.10), so size() on it
// shall report 0. Drive the empty-queue case end to end: overwrite a nonzero
// seed with the query result so the observed 0 proves size() actually ran and
// returned 0, rather than the variable merely retaining its default.
TEST(QueueSizeSimulation, EmptyQueueSizeIsZeroFromSource) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    sz = 99;\n"
      "    sz = q.size();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sz")->value.ToUint64(), 0u);
}

// size() is a live query: each call must report the queue's current element
// count, so growing and shrinking the queue between calls changes the result,
// including dropping back to zero once the queue is emptied by removal.
TEST(QueueSizeSimulation, SizeTracksLiveCount) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "size", {});

  ASSERT_TRUE(TryEvalQueueMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 2u);

  q->elements.push_back(MakeLogic4VecVal(f.arena, 32, 30));
  ASSERT_TRUE(TryEvalQueueMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 3u);

  q->elements.clear();
  ASSERT_TRUE(TryEvalQueueMethodCall(call, f.ctx, f.arena, out));
  EXPECT_EQ(out.ToUint64(), 0u);
}

}  // namespace
