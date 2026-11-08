#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

Expr* MakeXLiteral(Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->text = "1'bx";
  return e;
}

Expr* MakeQueueSlice(Arena& arena, std::string_view base, Expr* lo, Expr* hi) {
  auto* slice = arena.Create<Expr>();
  slice->kind = ExprKind::kSelect;
  slice->base = MakeId(arena, base);
  slice->index = lo;
  slice->index_end = hi;
  return slice;
}

void AssignSliceToDst(SimFixture& f, std::string_view dst, Expr* expr) {
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {expr};
  auto* stmt = MakeAssign(f.arena, dst, rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
}

TEST(QueueOps, IndexReturnsElement) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  auto result = EvalExpr(MakeSelect(f.arena, "q", 1), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

TEST(QueueOps, EmptyQueueSizeZero) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueOps, IndexFirstElement) {
  SimFixture f;
  MakeQueue(f, "q", {42, 99});
  auto result = EvalExpr(MakeSelect(f.arena, "q", 0), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(QueueOps, IndexLastElement) {
  SimFixture f;
  MakeQueue(f, "q", {42, 99, 7});
  auto result = EvalExpr(MakeSelect(f.arena, "q", 2), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

TEST(QueueOps, IndexedWriteUpdatesElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* lhs = MakeSelect(f.arena, "q", 1);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 55);
  bool ok = TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_TRUE(ok);
  EXPECT_EQ(q->elements[1].ToUint64(), 55u);
}

TEST(QueueOps, IndexedWriteOutOfBoundsIgnored) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto before = f.diag.WarningCount();
  auto* lhs = MakeSelect(f.arena, "q", 5);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
  EXPECT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueOps, AssignGrowsQueue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10});
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {MakeInt(f.arena, 1), MakeInt(f.arena, 2),
                   MakeInt(f.arena, 3)};
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
}

TEST(QueueOps, AssignShrinksQueue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30, 40});
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {MakeInt(f.arena, 5)};
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
}

TEST(QueueOps, SliceYieldsCorrectElements) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30, 40, 50});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 1), MakeInt(f.arena, 3)));

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 3u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
  EXPECT_EQ(dst->elements[1].ToUint64(), 30u);
  EXPECT_EQ(dst->elements[2].ToUint64(), 40u);
}

TEST(QueueOps, SliceAGreaterThanBYieldsEmpty) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {99});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 2), MakeInt(f.arena, 0)));

  auto* dst = f.ctx.FindQueue("dst");
  EXPECT_EQ(dst->elements.size(), 0u);
}

TEST(QueueOps, SliceSingleElementYieldsOneItem) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 1), MakeInt(f.arena, 1)));

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 1u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
}

TEST(QueueOps, SliceBBeyondDollarClampsToDollar) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 1), MakeInt(f.arena, 100)));

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 2u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
  EXPECT_EQ(dst->elements[1].ToUint64(), 30u);
}

TEST(QueueOps, BoundedQueueAssignTruncates) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {MakeInt(f.arena, 1), MakeInt(f.arena, 2),
                   MakeInt(f.arena, 3), MakeInt(f.arena, 4),
                   MakeInt(f.arena, 5)};
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
}

TEST(QueueOps, EmptyQueueReadReturnsX) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  auto result = EvalExpr(MakeSelect(f.arena, "q", 0), f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(QueueOps, EmptyQueueAssignEmptyConcat) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kConcatenation;
  rhs->elements = {};
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueOps, SliceFullRangeCopiesAll) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 0), MakeInt(f.arena, 2)));

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 3u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 10u);
  EXPECT_EQ(dst->elements[2].ToUint64(), 30u);
}

TEST(QueueOps, SliceXZBoundYieldsEmpty) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {99});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeXLiteral(f.arena), MakeInt(f.arena, 2)));

  auto* dst = f.ctx.FindQueue("dst");
  EXPECT_EQ(dst->elements.size(), 0u);
}

TEST(QueueOps, SliceNegativeLowSameAsZero) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q",
                     MakeUnary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 1)),
                     MakeInt(f.arena, 2)));

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_EQ(dst->elements.size(), 3u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 10u);
  EXPECT_EQ(dst->elements[2].ToUint64(), 30u);
}

TEST(QueueOps, SliceSingleOutOfRangeYieldsEmpty) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  MakeQueue(f, "dst", {99});

  AssignSliceToDst(
      f, "dst",
      MakeQueueSlice(f.arena, "q", MakeInt(f.arena, 5), MakeInt(f.arena, 5)));

  auto* dst = f.ctx.FindQueue("dst");
  EXPECT_EQ(dst->elements.size(), 0u);
}

TEST(QueueOps, IndexedWriteDollarPlusOneGrowsQueue) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto* lhs = MakeSelect(f.arena, "q", 2);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  bool ok = TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_TRUE(ok);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
}

TEST(QueueOps, IndexedWriteXZIndexIgnored) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto before = f.diag.WarningCount();
  auto* lhs =
      MakeSelectExpr(f.arena, MakeId(f.arena, "q"), MakeXLiteral(f.arena));
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueOps, NegativeIndexWriteIgnored) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20});
  auto before = f.diag.WarningCount();
  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kSelect;
  lhs->base = MakeId(f.arena, "q");
  lhs->index = MakeUnary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 1));
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueOps, XZIndexReadReturnsX) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  auto* sel =
      MakeSelectExpr(f.arena, MakeId(f.arena, "q"), MakeXLiteral(f.arena));
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(QueueOps, OutOfBoundsReadOfTwoStateQueueYieldsZero) {
  SimFixture f;
  auto* res = RunAndFindVar(
      "module t;\n"
      "  int q[$] = '{10, 20, 30};\n"
      "  logic [31:0] res;\n"
      "  initial res = q[5];\n"
      "endmodule\n",
      f, "res");
  ASSERT_NE(res, nullptr);
  EXPECT_TRUE(res->value.IsKnown());
  EXPECT_EQ(res->value.ToUint64(), 0u);
}

TEST(QueueOps, OutOfBoundsReadOfFourStateQueueYieldsX) {
  SimFixture f;
  auto* res = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q[$] = '{10, 20, 30};\n"
      "  logic [7:0] res;\n"
      "  initial res = q[5];\n"
      "endmodule\n",
      f, "res");
  ASSERT_NE(res, nullptr);
  EXPECT_FALSE(res->value.IsKnown());
}

TEST(QueueOps, UnknownIndexReadOfTwoStateQueueYieldsZero) {
  SimFixture f;
  auto* res = RunAndFindVar(
      "module t;\n"
      "  int q[$] = '{10, 20, 30};\n"
      "  logic [31:0] idx;\n"
      "  logic [31:0] res;\n"
      "  initial begin\n"
      "    idx = 32'bx;\n"
      "    res = q[idx];\n"
      "  end\n"
      "endmodule\n",
      f, "res");
  ASSERT_NE(res, nullptr);
  EXPECT_TRUE(res->value.IsKnown());
  EXPECT_EQ(res->value.ToUint64(), 0u);
}

TEST(QueueOps, SliceBoundsMayBeRuntimeVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{10, 20, 30, 40, 50};\n"
      "  int dst[$];\n"
      "  int lo, hi;\n"
      "  initial begin\n"
      "    lo = 1;\n"
      "    hi = 3;\n"
      "    dst = q[lo:hi];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* dst = f.ctx.FindQueue("dst");
  ASSERT_NE(dst, nullptr);
  ASSERT_EQ(dst->elements.size(), 3u);
  EXPECT_EQ(dst->elements[0].ToUint64(), 20u);
  EXPECT_EQ(dst->elements[1].ToUint64(), 30u);
  EXPECT_EQ(dst->elements[2].ToUint64(), 40u);
}

TEST(QueueOps, BoundedQueueFromSourceLimitsSize) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$:2];\n"
      "  initial q = {1, 2, 3, 4, 5};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 3u);
}

TEST(QueueOps, QueueInitializedByAssignmentPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$] = '{11, 22, 33};\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    a = q[0];\n"
      "    b = q[1];\n"
      "    c = q[2];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 22u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 33u);
}

TEST(QueueOps, QueueValueFromUnpackedArrayConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {44, 55, 66};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 44u);
  EXPECT_EQ(q->elements[1].ToUint64(), 55u);
  EXPECT_EQ(q->elements[2].ToUint64(), 66u);
}

TEST(QueueOps, XZIndexWriteWarningNames7_10_1) {
  SimFixture f;
  MakeQueue(f, "q", {31, 32});
  auto* lhs =
      MakeSelectExpr(f.arena, MakeId(f.arena, "q"), MakeXLiteral(f.arena));
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 33);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "queue write index contains x/z", 0, "7.10.1"));
}

TEST(QueueOps, OutOfBoundsWriteWarningNames7_10_1) {
  SimFixture f;
  MakeQueue(f, "q", {51, 52});
  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kSelect;
  lhs->base = MakeId(f.arena, "q");
  lhs->index = MakeUnary(f.arena, TokenKind::kMinus, MakeInt(f.arena, 2));
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 53);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "queue write index out of bounds", 0, "7.10.1"));
}

TEST(QueueOps, QueueDeclaredInProceduralBlockIsAQueue) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int n;\n"
      "  initial begin\n"
      "    int q[$];\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    n = q.size();\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 2u);
}

TEST(QueueOps, PushedElementsTakeTheElementWidth) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int n, s;\n"
      "  initial begin\n"
      "    logic signed [3:0] q[$];\n"
      "    q.push_back(12);\n"
      "    q.push_front(300);\n"
      "    q.insert(1, 4'sd7);\n"
      "    n = $bits(q[0]);\n"
      "    s = q[0] + q[1] + q[2];\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 4u);
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(static_cast<int32_t>(s->value.ToUint64()), -1);
}

TEST(QueueOps, DollarIndexedStatementsWriteLastAndAppend) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    q = '{1, 2, 3};\n"
      "    q[$] = 9;\n"
      "    q[$+1] = 4;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", q.size(), q[0], q[1], q[2], "
      "q[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 1 2 9 4\n");
}

}  // namespace
