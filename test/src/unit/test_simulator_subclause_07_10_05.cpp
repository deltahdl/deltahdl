#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "helpers_reported_error.h"
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

// §7.10.5: a write past a bounded queue's upper bound discards the
// out-of-bounds elements and issues a warning, so the report push_back raises
// enforces §7.10.5 and says so.
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

// §7.10.5: push_front pushes the queue's last element past the bound, which is
// the same rule reported at a different operation.
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

// §7.10.5: insert() likewise discards past the bound.
TEST(BoundedQueue, InsertDiscardWarningNames7_10_5) {
  SimFixture f;
  MakeBoundedQueue(f, 1, {5});
  auto* call = MakeMethodCall(f.arena, "q", "insert",
                              {MakeInt(f.arena, 0), MakeInt(f.arena, 6)});
  TryExecQueueMethodStmt(call, f.ctx, f.arena);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bounded queue overflow in insert", 0, "7.10.5"));
}

// §7.10.5: writing q[$+1] on a full bounded queue is the operator form of the
// same overflow.
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

// §7.10.5: an assignment whose value has more elements than the bound allows
// truncates and warns, the last of the five operations that reach the rule.
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

// Elaborates, lowers and runs `src`, then hands back the queue named "q" the
// run left behind, or nullptr when the source did not elaborate. The fixture
// is caller-owned, so `f.diag` stays inspectable and a case can name the
// report the run raised as well as the elements it kept.
QueueObject* RunAndFindQ(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return nullptr;
  LowerAndRun(design, f);
  return f.ctx.FindQueue("q");
}

// §7.10.5: "if, after any operation that writes to a bounded queue variable,
// that variable has any elements beyond its bound, then all such out-of-bounds
// elements shall be discarded". `new[3]` sizes a queue declared `[$:1]` past
// the two elements it may hold, so the third is dropped and the two the queue
// keeps are the first two of the initializing array.
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

// §7.10.5: the same discard "shall be issued" a warning, and the report the
// `new[]` on line 4 raises names §7.10.5 as the rule it enforces.
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

// §7.10.5: "Operations on bounded queues shall behave exactly as if the queue
// were unbounded except that" the bound is exceeded. `new[3]` on a queue
// declared `[$:3]` stays inside the four elements allowed, so nothing is
// discarded and no warning is issued.
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

// §7.10.5: a `new[]` that stands as a declaration's own initializer writes the
// variable just as an assignment in a procedure does, so the elements past the
// bound are discarded there too. `new[3]` without an initializing array leaves
// zero-filled elements, of which two survive.
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

// §7.10.5: the declaration-initializer form of `new[]` warns at the `new[3]`
// on line 2, under the same rule.
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

// §7.10.5: an unpacked array concatenation initializing a bounded queue at its
// declaration is an operation that writes the variable, so the third item is
// discarded and the two the queue keeps are the first two written.
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

// §7.10.5: the report the declaration initializer on line 2 raises names
// §7.10.5.
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

// §7.10.5: three items into a queue declared `[$:3]` fit inside the four
// elements allowed, so every item survives and no warning is issued.
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

// §7.10.5: "any operation that writes to a bounded queue variable" covers a
// nonblocking assignment, whose write lands when the update event runs rather
// than when the statement executes, so the source advances time before the
// queue is read back. The third item is discarded.
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

// §7.10.5: the warning the nonblocking update raises stands at the right-hand
// side on line 4 -- the statement that made the write, not the delay that let
// the update region run -- and names §7.10.5.
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

// §7.10.5: a nonblocking assignment of three items to a queue declared `[$:3]`
// stays inside the bound, so the update keeps every element and warns about
// nothing.
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

// §7.10.5 over the §11.4.14 dynamically sized target: a streaming
// concatenation assigned to a queue carves the stream into element-width
// slices, and 24 bits of stream make three `byte` elements. A queue declared
// `[$:1]` holds two, so the last slice is discarded and the two that survive
// carry the most significant bytes of the stream.
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

// §7.10.5: the report the streaming assignment on line 6 raises names §7.10.5.
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

// §7.10.5: the same 24-bit stream into a queue declared `[$:3]` makes three
// elements out of the four allowed, so every slice survives and no warning is
// issued.
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

// §7.10.5 over the §11.4.14.4 unpack: a streaming unpack whose target list
// names a queue sizes that queue from the stream bits the fixed targets leave,
// which is another operation that writes the variable. Three bytes reach a
// queue declared `[$:1]`, so the third is discarded while `trailer`, a fixed
// target, still receives its byte.
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

// §7.10.5: the report the streaming unpack on line 5 raises names §7.10.5.
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

// §7.10.5: the same unpack into a queue declared `[$:3]` gives it three of the
// four elements allowed, so nothing is discarded and no warning is issued.
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

// §7.10.5 over the §11.4.14.4 with-range unpack: `q with [0 +: 3]` names three
// slots of a queue declared `[$:1]`, and growing a queue to reach a slot is an
// operation that writes it, so the slot past the bound is discarded once the
// unpack has run.
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

// §7.10.5: the report the with-range unpack on line 4 raises names §7.10.5.
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

// §7.10.5: the same with-range unpack into a queue declared `[$:3]` reaches
// three of the four slots allowed, so nothing is discarded and no warning is
// issued.
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

}  // namespace
