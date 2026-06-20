#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §20.15.1 governs $q_initialize: the task that creates a stochastic-analysis
// queue from a q_id, a q_type drawn from Table 20-9, and a max_length
// capacity. The trailing `status` output (its codes owned by §20.15.6) is the
// observable channel through which the creation outcome is reported, so these
// tests drive each call through the evaluator and read back that status.

uint64_t RunQueueCall(SimFixture& f, std::string_view name,
                      std::vector<Expr*> args, std::string_view status_name) {
  auto* call = MkSysCall(f.arena, name, std::move(args));
  EvalExpr(call, f.ctx, f.arena);
  return f.ctx.FindVariable(status_name)->value.ToUint64();
}

// Invoke $q_initialize(q_id, q_type, max_length, status) and hand back the
// status it reported. A fresh status variable is seeded each time.
uint64_t Initialize(SimFixture& f, uint64_t q_id, int64_t q_type,
                    int64_t max_length) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(
      f, "$q_initialize",
      {MkInt(f.arena, q_id), MkInt(f.arena, static_cast<uint64_t>(q_type)),
       MkInt(f.arena, static_cast<uint64_t>(max_length)), MkId(f.arena, "st")},
      "st");
}

uint64_t Add(SimFixture& f, uint64_t q_id) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(f, "$q_add",
                      {MkInt(f.arena, q_id), MkInt(f.arena, 1),
                       MkInt(f.arena, 0), MkId(f.arena, "st")},
                      "st");
}

uint64_t Remove(SimFixture& f, uint64_t q_id) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(f, "$q_remove",
                      {MkInt(f.arena, q_id), MkInt(f.arena, 0),
                       MkInt(f.arena, 0), MkId(f.arena, "st")},
                      "st");
}

// Probe whether a queue exists: $q_full reports OK on a live queue and the
// undefined-q_id code on one that was never created.
uint64_t QueueDefined(SimFixture& f, uint64_t q_id) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(f, "$q_full", {MkInt(f.arena, q_id), MkId(f.arena, "st")},
                      "st");
}

// §20.15.1: $q_initialize creates a new queue. Before the call the q_id names
// nothing (undefined); after a well-formed call the queue exists. The
// successful q_type 1 creation here also witnesses Table 20-9 row 1
// (first-in, first-out) as a defined queue type.
TEST(QInitialize, CreatesNewQueue) {
  SimFixture f;
  EXPECT_NE(QueueDefined(f, 7), 0u);  // not yet created
  EXPECT_EQ(Initialize(f, 7, /*q_type=*/1, /*max_length=*/4), 0u);
  EXPECT_EQ(QueueDefined(f, 7), 0u);  // now a live queue
}

// §20.15.1 Table 20-9, row 2: q_type 2 (last-in, first-out) is the other
// defined queue type, so creation also succeeds.
TEST(QInitialize, LifoTypeIsAccepted) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, /*q_type=*/2, /*max_length=*/4), 0u);
}

// §20.15.1: q_type selects from Table 20-9, which defines only values 1 and 2.
// A value above that range is not a queue type, so no queue is created.
TEST(QInitialize, TypeOutsideTableCreatesNothing) {
  SimFixture f;
  EXPECT_NE(Initialize(f, 1, /*q_type=*/3, /*max_length=*/4), 0u);
  EXPECT_NE(QueueDefined(f, 1), 0u);  // creation did not register a queue
}

// §20.15.1 edge: the lower boundary of Table 20-9. q_type 0 sits just below the
// first defined type, so like any out-of-table value it names no queue type and
// creation registers nothing.
TEST(QInitialize, TypeBelowTableCreatesNothing) {
  SimFixture f;
  EXPECT_NE(Initialize(f, 1, /*q_type=*/0, /*max_length=*/4), 0u);
  EXPECT_NE(QueueDefined(f, 1), 0u);  // creation did not register a queue
}

// §20.15.1: max_length is the maximum number of entries allowed on the queue.
// A queue created with capacity 2 accepts exactly two entries; the third add
// finds it full, pinning the capacity to the supplied max_length.
TEST(QInitialize, MaxLengthBoundsTheEntryCount) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(Add(f, 1), 0u);  // entry 1 of 2
  EXPECT_EQ(Add(f, 1), 0u);  // entry 2 of 2 fills the queue
  EXPECT_NE(Add(f, 1), 0u);  // capacity reached, cannot add a third
}

// §20.15.1: the q_id shall uniquely identify the new queue, so a second
// $q_initialize re-using a live q_id cannot create another queue.
TEST(QInitialize, QidMustBeUnique) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 5, 1, 4), 0u);
  EXPECT_NE(Initialize(f, 5, 1, 4), 0u);
}

// §20.15.1: because the q_id identifies the queue, distinct q_ids name
// independent queues. An entry added under one id leaves the other empty.
TEST(QInitialize, DistinctQidsAreIndependentQueues) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, 1, 4), 0u);
  EXPECT_EQ(Initialize(f, 2, 1, 4), 0u);
  EXPECT_EQ(Add(f, 1), 0u);     // populate queue 1 only
  EXPECT_EQ(Remove(f, 1), 0u);  // queue 1 yields its entry
  EXPECT_NE(Remove(f, 2), 0u);  // queue 2 is still empty
}

}  // namespace
