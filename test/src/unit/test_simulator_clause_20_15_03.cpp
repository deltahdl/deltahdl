#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §20.15.3 governs $q_remove: the task that takes an entry off a stochastic-
// analysis queue. It takes a q_id selecting the source queue, returns the
// removed entry's job_id and inform_id through two integer outputs, and reports
// the outcome through a trailing `status` output (its codes owned by §20.15.6).
// The inform_id is whatever value the queue manager stored when §20.15.2 $q_add
// placed the entry; which entry is removed follows the FIFO/LIFO discipline of
// the q_type fixed at §20.15.1 $q_initialize. These tests drive the calls
// through the evaluator and read the outputs back from their variables.

uint64_t RunQueueCall(SimFixture& f, std::string_view name,
                      std::vector<Expr*> args, std::string_view status_name) {
  auto* call = MkSysCall(f.arena, name, std::move(args));
  EvalExpr(call, f.ctx, f.arena);
  return f.ctx.FindVariable(status_name)->value.ToUint64();
}

// $q_initialize(q_id, q_type, max_length, status): create the queue the remove
// tests operate on, returning the creation status.
uint64_t Initialize(SimFixture& f, uint64_t q_id, int64_t q_type,
                    int64_t max_length) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(f, "$q_initialize",
                      {MkInt(f.arena, q_id),
                       MkInt(f.arena, static_cast<uint64_t>(q_type)),
                       MkInt(f.arena, static_cast<uint64_t>(max_length)),
                       MkId(f.arena, "st")},
                      "st");
}

// $q_add(q_id, job_id, inform_id, status): place an entry carrying the given
// identifiers onto queue q_id, returning the reported status.
uint64_t Add(SimFixture& f, uint64_t q_id, uint64_t job_id, uint64_t inform_id) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(f, "$q_add",
                      {MkInt(f.arena, q_id), MkInt(f.arena, job_id),
                       MkInt(f.arena, inform_id), MkId(f.arena, "st")},
                      "st");
}

// $q_remove(q_id, job_id, inform_id, status): remove one entry from queue q_id.
// The job_id and inform_id are routed to caller-named variables so the outputs
// can be inspected; the call returns the reported status.
uint64_t Remove(SimFixture& f, uint64_t q_id, std::string_view job_var,
                std::string_view inform_var) {
  MakeVar(f, "st", 32, 0xDEAD);
  MakeVar(f, job_var, 32, 0xBEEF);
  MakeVar(f, inform_var, 32, 0xBEEF);
  return RunQueueCall(f, "$q_remove",
                      {MkInt(f.arena, q_id), MkId(f.arena, job_var),
                       MkId(f.arena, inform_var), MkId(f.arena, "st")},
                      "st");
}

uint64_t ReadVar(SimFixture& f, std::string_view name) {
  return f.ctx.FindVariable(name)->value.ToUint64();
}

// §20.15.3: $q_remove receives an entry from the queue named by q_id and
// returns it through the output arguments, reporting success. The job_id output
// identifies the removed entry and the inform_id output carries the value the
// queue manager stored during $q_add; its meaning is user-defined, so an
// arbitrary value placed at add time comes back unchanged at remove time.
TEST(QRemove, ReturnsInformIdStoredAtAdd) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 3, /*q_type=*/1, /*max_length=*/4), 0u);
  EXPECT_EQ(Add(f, 3, /*job_id=*/5, /*inform_id=*/9001), 0u);
  EXPECT_EQ(Remove(f, 3, "job", "inf"), 0u);
  EXPECT_EQ(ReadVar(f, "job"), 5u);
  EXPECT_EQ(ReadVar(f, "inf"), 9001u);
}

// §20.15.3: q_id selects which queue the entry is removed from. With two
// independent queues holding distinct entries, removing from each yields that
// queue's own entry.
TEST(QRemove, RemovesFromQueueSelectedByQid) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(Initialize(f, 2, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(Add(f, 1, /*job_id=*/11, /*inform_id=*/0), 0u);
  EXPECT_EQ(Add(f, 2, /*job_id=*/22, /*inform_id=*/0), 0u);
  EXPECT_EQ(Remove(f, 2, "job", "inf"), 0u);
  EXPECT_EQ(ReadVar(f, "job"), 22u);
  EXPECT_EQ(Remove(f, 1, "job", "inf"), 0u);
  EXPECT_EQ(ReadVar(f, "job"), 11u);
}

// §20.15.3: which entry is removed follows the queue discipline set by q_type.
// A FIFO queue (q_type 1) returns the oldest entry first.
TEST(QRemove, FifoQueueReturnsOldestEntryFirst) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 4, /*q_type=*/1, /*max_length=*/4), 0u);
  EXPECT_EQ(Add(f, 4, /*job_id=*/100, /*inform_id=*/0), 0u);
  EXPECT_EQ(Add(f, 4, /*job_id=*/200, /*inform_id=*/0), 0u);
  EXPECT_EQ(Remove(f, 4, "job", "inf"), 0u);
  EXPECT_EQ(ReadVar(f, "job"), 100u);  // first in, first out
  EXPECT_EQ(Remove(f, 4, "job", "inf"), 0u);
  EXPECT_EQ(ReadVar(f, "job"), 200u);
}

// §20.15.3: a LIFO queue (q_type 2) returns the most recently added entry
// first, demonstrating the removed entry is selected by the queue type.
TEST(QRemove, LifoQueueReturnsNewestEntryFirst) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 5, /*q_type=*/2, /*max_length=*/4), 0u);
  EXPECT_EQ(Add(f, 5, /*job_id=*/100, /*inform_id=*/0), 0u);
  EXPECT_EQ(Add(f, 5, /*job_id=*/200, /*inform_id=*/0), 0u);
  EXPECT_EQ(Remove(f, 5, "job", "inf"), 0u);
  EXPECT_EQ(ReadVar(f, "job"), 200u);  // last in, first out
  EXPECT_EQ(Remove(f, 5, "job", "inf"), 0u);
  EXPECT_EQ(ReadVar(f, "job"), 100u);
}

// §20.15.3: removing from a queue that holds no entry cannot return one, so the
// status reports an error (the Table 20-11 codes are §20.15.6's rule) rather
// than success.
TEST(QRemove, RemoveFromEmptyQueueReportsError) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 6, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_NE(Remove(f, 6, "job", "inf"), 0u);
}

// §20.15.3 edge: the q_id input must indicate a queue that exists. Aimed at an
// id that no $q_initialize ever created, $q_remove finds no queue to take an
// entry from and reports a non-success status instead of returning one.
TEST(QRemove, RemoveFromUndefinedQueueReportsError) {
  SimFixture f;
  EXPECT_NE(Remove(f, 99, "job", "inf"), 0u);
}

// §20.15.3: a successful $q_remove actually takes the entry off the queue. After
// the single stored entry is removed, the queue is empty, so an immediate
// second remove can no longer return an entry and reports an error — confirming
// the first remove consumed the entry rather than leaving it behind.
TEST(QRemove, SuccessfulRemoveConsumesTheEntry) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 8, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(Add(f, 8, /*job_id=*/77, /*inform_id=*/0), 0u);
  EXPECT_EQ(Remove(f, 8, "job", "inf"), 0u);  // the stored entry comes back
  EXPECT_EQ(ReadVar(f, "job"), 77u);
  EXPECT_NE(Remove(f, 8, "job", "inf"), 0u);  // nothing left to remove
}

}  // namespace
