#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

Expr* MakeConcat(Arena& arena, std::vector<Expr*> elems) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kConcatenation;
  e->elements = std::move(elems);
  return e;
}

QueueObject* MakeBoundedQueue(SimFixture& f, int32_t bound,
                              const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue("q", 32, bound);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  q->AssignFreshIds();
  return q;
}

TEST(BoundedQueue, PushBackRespectsMax) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, 3, {10, 20, 30});

  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 40)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
}

TEST(BoundedQueue, PushBackOnFullPreservesContents) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, 3, {10, 20, 30});

  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 40)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(BoundedQueue, PushBackWarnsOnDiscard) {
  SimFixture f;
  MakeBoundedQueue(f, 2, {10, 20});

  auto before = f.diag.WarningCount();
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 30)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(BoundedQueue, PushFrontRespectsMax) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, 3, {10, 20, 30});

  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 5)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
}

TEST(BoundedQueue, PushFrontDiscardsLastElement) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, 3, {10, 20, 30});

  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 5)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_EQ(q->elements[0].ToUint64(), 5u);
  EXPECT_EQ(q->elements[1].ToUint64(), 10u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
}

TEST(BoundedQueue, PushFrontWarnsOnDiscard) {
  SimFixture f;
  MakeBoundedQueue(f, 2, {10, 20});

  auto before = f.diag.WarningCount();
  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 5)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(BoundedQueue, InsertOnFullDiscardsLastElement) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, 3, {10, 20, 30});

  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 1), MakeInt(f.arena, 15)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 15u);
  EXPECT_EQ(q->elements[2].ToUint64(), 20u);
}

TEST(BoundedQueue, InsertWarnsOnDiscard) {
  SimFixture f;
  MakeBoundedQueue(f, 2, {10, 20});

  auto before = f.diag.WarningCount();
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 1), MakeInt(f.arena, 15)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(BoundedQueue, IndexedWriteDollarPlusOneOnFullIsNoop) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, 3, {10, 20, 30});

  auto* dollar = MakeId(f.arena, "$");
  auto* idx =
      MakeBinary(f.arena, TokenKind::kPlus, dollar, MakeInt(f.arena, 1));
  auto* lhs = MakeSelectExpr(f.arena, MakeId(f.arena, "q"), idx);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 40);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(BoundedQueue, IndexedWriteWarnsOnDiscard) {
  SimFixture f;
  MakeBoundedQueue(f, 2, {10, 20});

  auto before = f.diag.WarningCount();
  auto* dollar = MakeId(f.arena, "$");
  auto* idx =
      MakeBinary(f.arena, TokenKind::kPlus, dollar, MakeInt(f.arena, 1));
  auto* lhs = MakeSelectExpr(f.arena, MakeId(f.arena, "q"), idx);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 30);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(BoundedQueue, ConcatAssignTruncates) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 3);
  q->elements = {MakeLogic4VecVal(f.arena, 32, 10),
                 MakeLogic4VecVal(f.arena, 32, 20)};
  q->AssignFreshIds();

  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 30),
                                   MakeInt(f.arena, 40), MakeInt(f.arena, 50)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);

  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
}

TEST(BoundedQueue, ConcatAssignWarnsOnTruncate) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 2);
  q->elements = {MakeLogic4VecVal(f.arena, 32, 10)};
  q->AssignFreshIds();

  auto before = f.diag.WarningCount();
  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 20),
                                   MakeInt(f.arena, 30)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(BoundedQueue, AllowsPushAfterDelete) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, 3, {10, 20, 30});

  auto* del = MakeMethodCall(f.arena, "q", "delete", {MakeInt(f.arena, 0)});
  TryExecQueueMethodStmt(del, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 2u);

  auto* push =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 40)});
  TryExecQueueMethodStmt(push, f.ctx, f.arena);
  EXPECT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 40u);
}

TEST(BoundedQueue, UnboundedHasNoLimit) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32);
  for (int i = 0; i < 100; ++i) {
    auto* call = MakeMethodCall(f.arena, "q", "push_back",
                                {MakeInt(f.arena, static_cast<uint64_t>(i))});
    TryExecQueueMethodStmt(call, f.ctx, f.arena);
  }
  EXPECT_EQ(q->elements.size(), 100u);
}

TEST(BoundedQueue, BoundOfOneAllowsSingleElement) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 1);

  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 42)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);

  auto* call2 =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 99)});
  TryExecQueueMethodStmt(call2, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 1u);
  EXPECT_EQ(q->elements[0].ToUint64(), 42u);
}

TEST(BoundedQueue, AssignWithinBoundNoWarning) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 5);
  q->AssignFreshIds();
  auto before = f.diag.WarningCount();

  auto* rhs = MakeConcat(
      f.arena, {MakeInt(f.arena, 1), MakeInt(f.arena, 2), MakeInt(f.arena, 3)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(BoundedQueue, PushBackBelowBoundNoWarning) {
  SimFixture f;
  auto* q = MakeBoundedQueue(f, 3, {10});

  auto before = f.diag.WarningCount();
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 20)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(BoundedQueue, PushBackDiscardWarningNames7_10_5) {
  SimFixture f;
  MakeBoundedQueue(f, 1, {77});
  auto* call =
      MakeMethodCall(f.arena, "q", "push_back", {MakeInt(f.arena, 88)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in push_back", 0,
                              "7.10.5"));
}

TEST(BoundedQueue, PushFrontDiscardWarningNames7_10_5) {
  SimFixture f;
  MakeBoundedQueue(f, 1, {41});
  auto* call =
      MakeMethodCall(f.arena, "q", "push_front", {MakeInt(f.arena, 42)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in push_front", 0,
                              "7.10.5"));
}

TEST(BoundedQueue, InsertDiscardWarningNames7_10_5) {
  SimFixture f;
  MakeBoundedQueue(f, 1, {5});
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 0), MakeInt(f.arena, 6)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in insert", 0, "7.10.5"));
}

TEST(BoundedQueue, IndexedWriteDiscardWarningNames7_10_5) {
  SimFixture f;
  MakeBoundedQueue(f, 1, {9});
  auto* dollar = MakeId(f.arena, "$");
  auto* idx =
      MakeBinary(f.arena, TokenKind::kPlus, dollar, MakeInt(f.arena, 1));
  auto* lhs = MakeSelectExpr(f.arena, MakeId(f.arena, "q"), idx);
  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 12);
  TryQueueIndexedWrite(lhs, rhs_val, f.ctx, f.arena);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in indexed write", 0,
                              "7.10.5"));
}

TEST(BoundedQueue, ConcatAssignTruncateWarningNames7_10_5) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 32, 1);
  q->elements = {MakeLogic4VecVal(f.arena, 32, 3)};
  q->AssignFreshIds();
  auto* rhs = MakeConcat(f.arena, {MakeId(f.arena, "q"), MakeInt(f.arena, 4)});
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in assignment", 0,
                              "7.10.5"));
}

QueueObject* RunAndFindQ(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindQueue("q");
}

TEST(BoundedQueue, NewArrayInProcedureTruncatesToBound) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int src[$] = {10, 20, 30};\n"
      "  int q[$:1];\n"
      "  initial q = new[3](src);\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 10u);
  EXPECT_EQ(q->elements[1].ToUint64(), 20u);
}

TEST(BoundedQueue, NewArrayInProcedureWarningNames7_10_5) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int src[$] = {10, 20, 30};\n"
      "  int q[$:1];\n"
      "  initial q = new[3](src);\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in new[]", 4, "7.10.5"));
}

TEST(BoundedQueue, NewArrayWithinBoundNoWarning) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int src[$] = {10, 20, 30};\n"
      "  int q[$:3];\n"
      "  initial q = new[3](src);\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 30u);
  EXPECT_EQ(FindDiag(f, "bounded queue overflow"), nullptr);
}

TEST(BoundedQueue, NewArrayDeclInitTruncatesToBound) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int q[$:1] = new[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0u);
}

TEST(BoundedQueue, NewArrayDeclInitWarningNames7_10_5) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int q[$:1] = new[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in new[]", 2, "7.10.5"));
}

TEST(BoundedQueue, DeclInitTruncatesToBound) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int q[$:1] = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 1u);
  EXPECT_EQ(q->elements[1].ToUint64(), 2u);
}

TEST(BoundedQueue, DeclInitWarningNames7_10_5) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int q[$:1] = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "bounded queue overflow in declaration initializer",
      2, "7.10.5"));
}

TEST(BoundedQueue, DeclInitWithinBoundNoWarning) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int q[$:3] = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 3u);
  EXPECT_EQ(FindDiag(f, "bounded queue overflow"), nullptr);
}

TEST(BoundedQueue, NonblockingAssignTruncatesToBound) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int q[$:1];\n"
      "  initial begin\n"
      "    q <= {1, 2, 3};\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 1u);
  EXPECT_EQ(q->elements[1].ToUint64(), 2u);
}

TEST(BoundedQueue, NonblockingAssignWarningNames7_10_5) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int q[$:1];\n"
      "  initial begin\n"
      "    q <= {1, 2, 3};\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "bounded queue overflow in nonblocking assignment",
      4, "7.10.5"));
}

TEST(BoundedQueue, NonblockingAssignWithinBoundNoWarning) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  int q[$:3];\n"
      "  initial begin\n"
      "    q <= {1, 2, 3};\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 3u);
  EXPECT_EQ(FindDiag(f, "bounded queue overflow"), nullptr);
}

TEST(BoundedQueue, StreamingAssignTruncatesToBound) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  byte q[$:1];\n"
      "  logic [23:0] src;\n"
      "  initial begin\n"
      "    src = 24'hAABBCC;\n"
      "    q = {>> {src}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0xAAu);
  EXPECT_EQ(q->elements[1].ToUint64(), 0xBBu);
}

TEST(BoundedQueue, StreamingAssignWarningNames7_10_5) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  byte q[$:1];\n"
      "  logic [23:0] src;\n"
      "  initial begin\n"
      "    src = 24'hAABBCC;\n"
      "    q = {>> {src}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in streaming assignment",
                              6, "7.10.5"));
}

TEST(BoundedQueue, StreamingAssignWithinBoundNoWarning) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  byte q[$:3];\n"
      "  logic [23:0] src;\n"
      "  initial begin\n"
      "    src = 24'hAABBCC;\n"
      "    q = {>> {src}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 0xCCu);
  EXPECT_EQ(FindDiag(f, "bounded queue overflow"), nullptr);
}

TEST(BoundedQueue, StreamingUnpackTargetTruncatesToBound) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  byte q[$:1];\n"
      "  logic [7:0] trailer;\n"
      "  initial begin\n"
      "    {>> byte {q, trailer}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0xAAu);
  EXPECT_EQ(q->elements[1].ToUint64(), 0xBBu);
  EXPECT_EQ(f.ctx.FindVariable("trailer")->value.ToUint64(), 0xDDu);
}

TEST(BoundedQueue, StreamingUnpackTargetWarningNames7_10_5) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  byte q[$:1];\n"
      "  logic [7:0] trailer;\n"
      "  initial begin\n"
      "    {>> byte {q, trailer}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in streaming assignment",
                              5, "7.10.5"));
}

TEST(BoundedQueue, StreamingUnpackTargetWithinBoundNoWarning) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  byte q[$:3];\n"
      "  logic [7:0] trailer;\n"
      "  initial begin\n"
      "    {>> byte {q, trailer}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(q->elements[2].ToUint64(), 0xCCu);
  EXPECT_EQ(FindDiag(f, "bounded queue overflow"), nullptr);
}

TEST(BoundedQueue, StreamingUnpackWithRangeTruncatesToBound) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  byte q[$:1];\n"
      "  initial begin\n"
      "    {<< byte {q with [0 +: 3]}} = 24'hAABBCC;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 2u);
}

TEST(BoundedQueue, StreamingUnpackWithRangeWarningNames7_10_5) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  byte q[$:1];\n"
      "  initial begin\n"
      "    {<< byte {q with [0 +: 3]}} = 24'hAABBCC;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in streaming assignment",
                              4, "7.10.5"));
}

TEST(BoundedQueue, StreamingUnpackWithRangeWithinBoundNoWarning) {
  SimFixture f;
  auto* q = RunAndFindQ(
      "module t;\n"
      "  byte q[$:3];\n"
      "  initial begin\n"
      "    {<< byte {q with [0 +: 3]}} = 24'hAABBCC;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 3u);
  EXPECT_EQ(FindDiag(f, "bounded queue overflow"), nullptr);
}

TEST(BoundedQueue, BlockScopedBoundTruncatesPushBack) {
  const char* src =
      "module t;\n"
      "  int n, e0, e1;\n"
      "  initial begin\n"
      "    int q[$:1];\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    q.push_back(30);\n"
      "    n = q.size();\n"
      "    e0 = q[0];\n"
      "    e1 = q[1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 2u);
  EXPECT_EQ(RunAndGet(src, "e0"), 10u);
  EXPECT_EQ(RunAndGet(src, "e1"), 20u);
}

TEST(BoundedQueue, BlockScopedBoundWarningNames7_10_5) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    int q[$:1];\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    q.push_back(30);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in push_back", 6,
                              "7.10.5"));
}

TEST(BoundedQueue, BoundedQueuePropertyDiscardsBeyondItsBound) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int q[$:2];\n"
                      "  function void push(int x);\n"
                      "    q.push_back(x);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    static C c = new;\n"
                      "    c.push(1);\n"
                      "    c.push(2);\n"
                      "    c.push(3);\n"
                      "    c.push(4);\n"
                      "    out = c.q.size() * 10 + c.q[$];\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            33u);
}

}  // namespace
