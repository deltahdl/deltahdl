#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

void RunRefOpThenWrite(SimFixture& f, std::vector<Stmt*> op_stmts,
                       Expr* ref_arg) {
  op_stmts.push_back(MakeAssign(f.arena, "v", MakeInt(f.arena, 99)));
  RegAutoFunc(f, "test_fn",
              {{Direction::kRef, false, false, false, {}, "v", nullptr, {}}},
              std::move(op_stmts));
  auto* call = MakeCall(f.arena, "test_fn", {ref_arg});
  EvalExpr(call, f.ctx, f.arena);
}

Expr* MakeMemberAccess(Arena& arena, std::string_view obj,
                       std::string_view field) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kMemberAccess;
  e->lhs = MakeId(arena, obj);
  e->rhs = MakeId(arena, field);
  return e;
}

Expr* MakeSlice(Arena& arena, std::string_view name, Expr* lo, Expr* hi) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = MakeId(arena, name);
  e->index = lo;
  e->index_end = hi;
  return e;
}

Expr* MakeEmptyConcat(Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kConcatenation;
  return e;
}

Expr* MakeNewSized(Arena& arena, uint64_t size) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kCall;
  e->text = "new";
  e->args.push_back(MakeInt(arena, size));
  return e;
}

struct QueueAcrossRun {
  QueueObject* q;
  std::vector<uint64_t> ids_before;
};

QueueAcrossRun RunAndCaptureIds(const char* src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  if (!design) return {nullptr, {}};
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* q = f.ctx.FindQueue("q");
  std::vector<uint64_t> before;
  if (q) before = q->element_ids;
  f.scheduler.Run();
  return {q, before};
}

bool AnyIdSurvives(const QueueAcrossRun& r) {
  return std::any_of(
      r.ids_before.begin(), r.ids_before.end(), [&](uint64_t id) {
        return std::find(r.q->element_ids.begin(), r.q->element_ids.end(),
                         id) != r.q->element_ids.end();
      });
}

void ExpectPrependKeepsRefValid(SimFixture& f, Stmt* op_stmt) {
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(f, {op_stmt}, MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
  EXPECT_EQ(q->elements[3].ToUint64(), 30u);
}

TEST(QueueRefPersistence, DeleteOutdatesRemovedElementRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete",
                                            {MakeInt(f.arena, 1)}))},
      MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRefPersistence, DeleteLeavesOtherElementRefValid) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete",
                                            {MakeInt(f.arena, 1)}))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 99u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRefPersistence, DeleteAllOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "delete", {}))},
      MakeSelect(f.arena, "q", 1));

  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueRefPersistence, PopFrontOutdatesPoppedElementRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_front", {}))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRefPersistence, PopFrontLeavesRemainingRefValid) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_front", {}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

TEST(QueueRefPersistence, PopBackOutdatesPoppedElementRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_back", {}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueRefPersistence, PopBackLeavesRemainingRefValid) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "pop_back", {}))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 99u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(QueueRefPersistence, InsertNeverOutdatesExistingRef) {
  SimFixture f;
  ExpectPrependKeepsRefValid(
      f, MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "insert",
                                              {MakeInt(f.arena, 0),
                                               MakeInt(f.arena, 5)})));
}

TEST(QueueRefPersistence, PushBackNeverOutdatesExistingRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                            {MakeInt(f.arena, 40)}))},
      MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[1].ToUint64(), 99u);
}

TEST(QueueRefPersistence, PushFrontNeverOutdatesExistingRef) {
  SimFixture f;
  ExpectPrependKeepsRefValid(
      f, MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_front",
                                              {MakeInt(f.arena, 5)})));
}

TEST(QueueRefPersistence, BoundedInsertOutdatesDroppedTailRef) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  for (auto v : {10u, 20u, 30u})
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  q->AssignFreshIds();

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(
          f.arena, MakeMethodCall(f.arena, "q", "insert",
                                  {MakeInt(f.arena, 0), MakeInt(f.arena, 5)}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
}

TEST(QueueRefPersistence, BoundedPushFrontOutdatesDroppedTailRef) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  for (auto v : {10u, 20u, 30u})
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  q->AssignFreshIds();

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_front",
                                            {MakeInt(f.arena, 5)}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
}

TEST(QueueRefPersistence, BoundedPushBackNeverOutdatesExistingRef) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  for (auto v : {10u, 20u, 30u})
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  q->AssignFreshIds();

  RunRefOpThenWrite(
      f,
      {MakeExprStmt(f.arena, MakeMethodCall(f.arena, "q", "push_back",
                                            {MakeInt(f.arena, 40)}))},
      MakeSelect(f.arena, "q", 2));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
}

TEST(QueueRefPersistence, ConcatAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements = {MakeId(f.arena, "q"), MakeInt(f.arena, 40)};

  RunRefOpThenWrite(f, {MakeAssign(f.arena, "q", concat)},
                    MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(q->elements[3].ToUint64(), 40u);
}

TEST(QueueRefPersistence, SortLeavesRefFollowingItsElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {30, 10, 20});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMemberAccess(f.arena, "q", "sort"))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
}

TEST(QueueRefPersistence, RsortLeavesRefFollowingItsElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 30, 20});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMemberAccess(f.arena, "q", "rsort"))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 30u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
}

TEST(QueueRefPersistence, ReverseLeavesRefFollowingItsElement) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMemberAccess(f.arena, "q", "reverse"))},
      MakeSelect(f.arena, "q", 0));

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 30u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 99u);
}

TEST(QueueRefPersistence, ShuffleLeavesRefValid) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(
      f, {MakeExprStmt(f.arena, MakeMemberAccess(f.arena, "q", "shuffle"))},
      MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 3u);
  size_t wrote = 0, kept = 0;
  for (const auto& e : q->elements) {
    if (e.ToUint64() == 99u) ++wrote;
    if (e.ToUint64() == 20u) ++kept;
  }
  EXPECT_EQ(wrote, 1u);
  EXPECT_EQ(kept, 0u);
}

TEST(QueueRefPersistence, SliceAssignOutdatesEvenSurvivingElementRef) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(f,
                    {MakeAssign(f.arena, "q",
                                MakeSlice(f.arena, "q", MakeInt(f.arena, 1),
                                          MakeId(f.arena, "$")))},
                    MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 20u);
  EXPECT_EQ(q->elements[1].ToUint64(), 30u);
}

TEST(QueueRefPersistence, EmptyConcatAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(f, {MakeAssign(f.arena, "q", MakeEmptyConcat(f.arena))},
                    MakeSelect(f.arena, "q", 1));

  EXPECT_EQ(q->elements.size(), 0u);
}

TEST(QueueRefPersistence, NewSizedAssignOutdatesAllRefs) {
  SimFixture f;
  auto* q = MakeQueue(f, "q", {10, 20, 30});

  RunRefOpThenWrite(f, {MakeAssign(f.arena, "q", MakeNewSized(f.arena, 2))},
                    MakeSelect(f.arena, "q", 1));

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0u);
}

TEST(QueueRefPersistence, GreedyStreamUnpackOutdatesAllRefs) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte q[$] = {8'h11, 8'h22, 8'h33};\n"
      "  logic [7:0] trailer;\n"
      "  initial begin\n"
      "    {>> byte {q, trailer}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  ASSERT_EQ(r.ids_before.size(), 3u);
  EXPECT_FALSE(AnyIdSurvives(r));
}

TEST(QueueRefPersistence, GreedyStreamUnpackGivesEveryElementAnIdentity) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte q[$] = {8'h11, 8'h22, 8'h33};\n"
      "  logic [7:0] trailer;\n"
      "  initial begin\n"
      "    {>> byte {q, trailer}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  EXPECT_EQ(r.q->element_ids.size(), r.q->elements.size());
}

TEST(QueueRefPersistence, SecondStreamQueueEmptiedOutdatesAllRefs) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte p[$];\n"
      "  byte q[$] = {8'h11, 8'h22, 8'h33};\n"
      "  initial begin\n"
      "    {>> byte {p, q}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  ASSERT_EQ(r.ids_before.size(), 3u);
  EXPECT_TRUE(r.q->element_ids.empty());
}

TEST(QueueRefPersistence, WithRangeStreamUnpackKeepsExistingIdentities) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte q[$] = {8'h11, 8'h22};\n"
      "  initial begin\n"
      "    {<< byte {q with [0 +: 4]}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  ASSERT_EQ(r.ids_before.size(), 2u);
  ASSERT_GE(r.q->element_ids.size(), 2u);
  EXPECT_EQ(r.q->element_ids[0], r.ids_before[0]);
  EXPECT_EQ(r.q->element_ids[1], r.ids_before[1]);
}

TEST(QueueRefPersistence, WithRangeStreamUnpackGivesGrownElementsIdentities) {
  SimFixture f;
  auto r = RunAndCaptureIds(
      "module t;\n"
      "  byte q[$] = {8'h11, 8'h22};\n"
      "  initial begin\n"
      "    {<< byte {q with [0 +: 4]}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(r.q, nullptr);
  EXPECT_EQ(r.q->element_ids.size(), r.q->elements.size());
}

}  // namespace
