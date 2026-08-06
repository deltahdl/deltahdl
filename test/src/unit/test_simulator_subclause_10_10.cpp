#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

Expr* MakeConcat(Arena& arena, std::vector<Expr*> elems) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kConcatenation;
  e->elements = std::move(elems);
  return e;
}

TEST(UnpackedArrayConcatSim, LeftToRightArrangement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[1:3];\n"
      "  initial A = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a1 = f.ctx.FindVariable("A[1]");
  auto* a2 = f.ctx.FindVariable("A[2]");
  auto* a3 = f.ctx.FindVariable("A[3]");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  ASSERT_NE(a3, nullptr);
  EXPECT_EQ(a1->value.ToUint64(), 10u);
  EXPECT_EQ(a2->value.ToUint64(), 20u);
  EXPECT_EQ(a3->value.ToUint64(), 30u);
}

TEST(UnpackedArrayConcatSim, EmptyConcatClearsQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  initial q = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->elements.empty());
}

TEST(UnpackedArrayConcatSim, ConcatToQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

// An item whose self-determined type is an unpacked array of the target's
// element type contributes its members, preserving their internal left-to-
// right order. Joining two such items shall give a queue with the first
// item's members followed by the second item's members.
TEST(UnpackedArrayConcatSim, ConcatWithArrayItemsExpandsLeftToRight) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[0:1] = '{10, 20};\n"
      "  int B[0:1] = '{30, 40};\n"
      "  int q[$];\n"
      "  initial q = {A, B};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 40u);
}

TEST(UnpackedArrayConcatSim, ConcatToDynamicArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  initial d = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("d");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(UnpackedArrayConcatSim, EmptyConcatToFixedSizeError) {
  SimFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_descending = false;
  f.ctx.RegisterArray("A", info);
  for (uint32_t i = 0; i < 3; ++i)
    f.ctx.CreateVariable("A[" + std::to_string(i) + "]", 32);
  auto* rhs = MakeConcat(f.arena, {});
  auto* stmt = MakeAssign(f.arena, "A", rhs);
  TryArrayBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §10.10: "It shall be an error if the size of the resulting array differs from
// the number of elements in a fixed-size target." The size-mismatch rule is a
// runtime rule that fires only when the fixed-size target and the concatenation
// meet in a procedural assignment, so it must be driven from real source (a
// declaration + an initial-block assignment) rather than from a hand-built
// ArrayInfo. Elaboration stays clean; the error appears when the assignment
// runs.
TEST(UnpackedArrayConcatSim, FixedSizeMismatchFromSourceErrorsAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3, 4};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
}

// §10.10: "If the size exceeds the maximum number of elements of a bounded
// queue, then elements beyond the upper bound of the target shall be ignored
// and a warning shall be issued." The bound comes from the queue_dimension of
// §7.10 (`[$:1]` → capacity 2), so this weaves §7.10's bounded-queue target
// with §10.10's overflow rule and is driven end to end from source: the third
// item is dropped and a warning is raised, leaving exactly two elements.
TEST(UnpackedArrayConcatSim, BoundedQueueOverflowFromSourceTruncatesAndWarns) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$:1];\n"
      "  initial q = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto warnings_before = f.diag.WarningCount();
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_GT(f.diag.WarningCount(), warnings_before);
}

}  // namespace
