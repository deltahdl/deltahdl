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

// ---------------------------------------------------------------------------
// Full-pipeline tests
// ---------------------------------------------------------------------------

TEST(UnpackedArrayConcatSim, ScalarItemsToFixedArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[0:2];\n"
      "  initial A = {10, 20, 30};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a0 = f.ctx.FindVariable("A[0]");
  auto* a1 = f.ctx.FindVariable("A[1]");
  auto* a2 = f.ctx.FindVariable("A[2]");
  ASSERT_NE(a0, nullptr);
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  EXPECT_EQ(a0->value.ToUint64(), 10u);
  EXPECT_EQ(a1->value.ToUint64(), 20u);
  EXPECT_EQ(a2->value.ToUint64(), 30u);
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

// ---------------------------------------------------------------------------
// Size-mismatch errors for fixed-size targets
// ---------------------------------------------------------------------------

TEST(UnpackedArrayConcatSim, FixedSizeTooFewElementsError) {
  SimFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_descending = false;
  f.ctx.RegisterArray("A", info);
  for (uint32_t i = 0; i < 3; ++i)
    f.ctx.CreateVariable("A[" + std::to_string(i) + "]", 32);
  auto* rhs = MakeConcat(f.arena, {MakeInt(f.arena, 1), MakeInt(f.arena, 2)});
  auto* stmt = MakeAssign(f.arena, "A", rhs);
  TryArrayBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UnpackedArrayConcatSim, FixedSizeTooManyElementsError) {
  SimFixture f;
  ArrayInfo info;
  info.lo = 0;
  info.size = 3;
  info.elem_width = 32;
  info.is_descending = false;
  f.ctx.RegisterArray("A", info);
  for (uint32_t i = 0; i < 3; ++i)
    f.ctx.CreateVariable("A[" + std::to_string(i) + "]", 32);
  auto* rhs = MakeConcat(
      f.arena, {MakeInt(f.arena, 1), MakeInt(f.arena, 2),
                MakeInt(f.arena, 3), MakeInt(f.arena, 4)});
  auto* stmt = MakeAssign(f.arena, "A", rhs);
  TryArrayBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_TRUE(f.diag.HasErrors());
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

// ---------------------------------------------------------------------------
// Bounded queue overflow
// ---------------------------------------------------------------------------

TEST(UnpackedArrayConcatSim, BoundedQueueOverflowTruncates) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  auto* rhs = MakeConcat(
      f.arena, {MakeInt(f.arena, 10), MakeInt(f.arena, 20),
                MakeInt(f.arena, 30), MakeInt(f.arena, 40)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(UnpackedArrayConcatSim, BoundedQueueOverflowWarns) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32, 2);
  auto before = f.diag.WarningCount();
  auto* rhs = MakeConcat(
      f.arena, {MakeInt(f.arena, 10), MakeInt(f.arena, 20),
                MakeInt(f.arena, 30)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

}  // namespace
