#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_stochastic_queue.h"
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

// §20.15.2: $q_add places an entry on the named queue. Against a freshly
// created queue with spare capacity the add succeeds, reported as the Table
// 20-11 success status.
TEST(QAdd, PlacesEntryAndReportsSuccess) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 7, /*q_type=*/1, /*max_length=*/4), 0u);
  EXPECT_EQ(QAdd(f, 7), 0u);
}

// §20.15.2: the q_id argument indicates which queue receives the entry. An
// add aimed at a q_id that no $q_initialize ever created cannot place an
// entry, so it reports a non-success status.
TEST(QAdd, AddToUndefinedQueueReportsError) {
  SimFixture f;
  EXPECT_NE(QAdd(f, 99), 0u);
}

// §20.15.2: because q_id selects the queue, adds routed to different ids land
// in independent queues. Filling queue 1 to capacity leaves queue 2, which
// shares the same max_length, still able to accept an entry.
TEST(QAdd, AddRoutesToQueueByQid) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 1, /*q_type=*/1, /*max_length=*/1), 0u);
  EXPECT_EQ(QInitialize(f, 2, /*q_type=*/1, /*max_length=*/1), 0u);
  EXPECT_EQ(QAdd(f, 1), 0u);  // queue 1 now full
  EXPECT_NE(QAdd(f, 1), 0u);  // queue 1 rejects a second entry
  EXPECT_EQ(QAdd(f, 2), 0u);  // queue 2 untouched, still accepts one
}

// §20.15.2 edge: an add rejected because the queue is full must not place an
// entry. The rejected add still reports the full status, and the occupancy is
// left at one, so exactly one remove succeeds and the second finds the queue
// empty.
TEST(QAdd, RejectedAddDoesNotPlaceEntry) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 4, /*q_type=*/1, /*max_length=*/1), 0u);
  EXPECT_EQ(QAdd(f, 4), 0u);           // single allowed entry
  EXPECT_NE(QAdd(f, 4), 0u);           // rejected: queue full
  EXPECT_EQ(QRemoveStatus(f, 4), 0u);  // the one real entry comes back
  EXPECT_NE(QRemoveStatus(f, 4),
            0u);  // empty: the rejected add left nothing behind
}

// §20.15.2: job_id and inform_id are integer inputs describing the entry; the
// inform_id meaning is user-defined. $q_add accepts arbitrary integer values
// for both and still places the entry, so each add below succeeds regardless
// of the descriptive values carried.
TEST(QAdd, AcceptsJobIdAndInformIdInputs) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 8, /*q_type=*/1, /*max_length=*/3), 0u);
  EXPECT_EQ(QAdd(f, 8, /*job_id=*/42, /*inform_id=*/100), 0u);
  EXPECT_EQ(QAdd(f, 8, /*job_id=*/0, /*inform_id=*/0), 0u);
  EXPECT_EQ(QAdd(f, 8, /*job_id=*/7, /*inform_id=*/999), 0u);
}

}  // namespace
