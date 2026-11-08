#include <gtest/gtest.h>

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
