#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §20.15.2 governs $q_add: the task that places an entry onto a stochastic-
// analysis queue. It takes a q_id selecting the target queue, a job_id and an
// inform_id describing the entry, and a trailing `status` output (its codes
// owned by §20.15.6) that reports the outcome. The queue managed here is the
// one created by §20.15.1 $q_initialize. These tests drive each call through
// the evaluator and read back the reported status; queue occupancy is observed
// indirectly through the full/empty conditions that the status code exposes.

uint64_t RunQueueCall(SimFixture& f, std::string_view name,
                      std::vector<Expr*> args, std::string_view status_name) {
  auto* call = MkSysCall(f.arena, name, std::move(args));
  EvalExpr(call, f.ctx, f.arena);
  return f.ctx.FindVariable(status_name)->value.ToUint64();
}

// $q_initialize(q_id, q_type, max_length, status): create the queue the add
// tests operate on, returning the creation status.
uint64_t Initialize(SimFixture& f, uint64_t q_id, int64_t q_type,
                    int64_t max_length) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(
      f, "$q_initialize",
      {MkInt(f.arena, q_id), MkInt(f.arena, static_cast<uint64_t>(q_type)),
       MkInt(f.arena, static_cast<uint64_t>(max_length)), MkId(f.arena, "st")},
      "st");
}

// $q_add(q_id, job_id, inform_id, status): place an entry carrying the given
// job_id and inform_id onto queue q_id, returning the reported status.
uint64_t Add(SimFixture& f, uint64_t q_id, uint64_t job_id = 1,
             uint64_t inform_id = 0) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(f, "$q_add",
                      {MkInt(f.arena, q_id), MkInt(f.arena, job_id),
                       MkInt(f.arena, inform_id), MkId(f.arena, "st")},
                      "st");
}

// $q_remove(q_id, job_id, inform_id, status): used here only to drain entries
// so the resulting occupancy can be observed through its status.
uint64_t Remove(SimFixture& f, uint64_t q_id) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(f, "$q_remove",
                      {MkInt(f.arena, q_id), MkInt(f.arena, 0),
                       MkInt(f.arena, 0), MkId(f.arena, "st")},
                      "st");
}

// §20.15.2: $q_add places an entry on the named queue. Against a freshly
// created queue with spare capacity the add succeeds, reported as the Table
// 20-11 success status.
TEST(QAdd, PlacesEntryAndReportsSuccess) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 7, /*q_type=*/1, /*max_length=*/4), 0u);
  EXPECT_EQ(Add(f, 7), 0u);
}

// §20.15.2: the q_id argument indicates which queue receives the entry. An
// add aimed at a q_id that no $q_initialize ever created cannot place an
// entry, so it reports a non-success status.
TEST(QAdd, AddToUndefinedQueueReportsError) {
  SimFixture f;
  EXPECT_NE(Add(f, 99), 0u);
}

// §20.15.2: because q_id selects the queue, adds routed to different ids land
// in independent queues. Filling queue 1 to capacity leaves queue 2, which
// shares the same max_length, still able to accept an entry.
TEST(QAdd, AddRoutesToQueueByQid) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, /*q_type=*/1, /*max_length=*/1), 0u);
  EXPECT_EQ(Initialize(f, 2, /*q_type=*/1, /*max_length=*/1), 0u);
  EXPECT_EQ(Add(f, 1), 0u);  // queue 1 now full
  EXPECT_NE(Add(f, 1), 0u);  // queue 1 rejects a second entry
  EXPECT_EQ(Add(f, 2), 0u);  // queue 2 untouched, still accepts one
}

// §20.15.2 edge: an add rejected because the queue is full must not place an
// entry. The rejected add still reports the full status, and the occupancy is
// left at one, so exactly one remove succeeds and the second finds the queue
// empty.
TEST(QAdd, RejectedAddDoesNotPlaceEntry) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 4, /*q_type=*/1, /*max_length=*/1), 0u);
  EXPECT_EQ(Add(f, 4), 0u);     // single allowed entry
  EXPECT_NE(Add(f, 4), 0u);     // rejected: queue full
  EXPECT_EQ(Remove(f, 4), 0u);  // the one real entry comes back
  EXPECT_NE(Remove(f, 4), 0u);  // empty: the rejected add left nothing behind
}

// §20.15.2: job_id and inform_id are integer inputs describing the entry; the
// inform_id meaning is user-defined. $q_add accepts arbitrary integer values
// for both and still places the entry, so each add below succeeds regardless
// of the descriptive values carried.
TEST(QAdd, AcceptsJobIdAndInformIdInputs) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 8, /*q_type=*/1, /*max_length=*/3), 0u);
  EXPECT_EQ(Add(f, 8, /*job_id=*/42, /*inform_id=*/100), 0u);
  EXPECT_EQ(Add(f, 8, /*job_id=*/0, /*inform_id=*/0), 0u);
  EXPECT_EQ(Add(f, 8, /*job_id=*/7, /*inform_id=*/999), 0u);
}

}  // namespace
