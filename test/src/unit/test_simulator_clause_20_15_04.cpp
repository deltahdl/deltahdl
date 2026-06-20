#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_stochastic_queue.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §20.15.4 governs $q_full: the system function that reports whether a
// stochastic-analysis queue has room for another entry. It takes a q_id
// selecting the queue and returns 1 when the queue is full and 0 when it is
// not, while reporting the operation outcome through a trailing `status` output
// (whose Table 20-11 codes are owned by §20.15.6). These tests fill a queue to
// its capacity (fixed at §20.15.1 $q_initialize) using §20.15.2 $q_add and read
// the function's return value back from the evaluated call.

// §20.15.4: a freshly created queue holding no entries has room, so $q_full
// returns 0 (the queue is not full).
TEST(QFull, EmptyQueueIsNotFull) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 1, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(QFullValue(f, 1, "st"), 0u);
}

// §20.15.4: a queue that holds fewer entries than its capacity still has room,
// so $q_full returns 0.
TEST(QFull, PartiallyFilledQueueIsNotFull) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 2, /*q_type=*/1, /*max_length=*/3), 0u);
  EXPECT_EQ(QAdd(f, 2, /*job_id=*/10, /*inform_id=*/0), 0u);
  EXPECT_EQ(QFullValue(f, 2, "st"), 0u);
}

// §20.15.4: once the queue holds as many entries as its capacity allows, there
// is no room for another entry, so $q_full returns 1.
TEST(QFull, FullQueueReturnsOne) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 3, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(QAdd(f, 3, /*job_id=*/10, /*inform_id=*/0), 0u);
  EXPECT_EQ(QAdd(f, 3, /*job_id=*/20, /*inform_id=*/0), 0u);
  EXPECT_EQ(QFullValue(f, 3, "st"), 1u);
}

// §20.15.4: a single-entry queue is full as soon as its one slot is occupied,
// confirming the result tracks capacity rather than a fixed threshold.
TEST(QFull, SingleEntryQueueIsFullAfterOneAdd) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 4, /*q_type=*/1, /*max_length=*/1), 0u);
  EXPECT_EQ(QFullValue(f, 4, "st"), 0u);
  EXPECT_EQ(QAdd(f, 4, /*job_id=*/7, /*inform_id=*/0), 0u);
  EXPECT_EQ(QFullValue(f, 4, "st"), 1u);
}

// §20.15.4: fullness reflects the queue's current occupancy, not a one-way
// latch. A queue filled to capacity reports full (1); after an entry is taken
// off it again has room, so $q_full reports not full (0).
TEST(QFull, ReportsNotFullAfterEntryRemoved) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 5, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(QAdd(f, 5, /*job_id=*/1, /*inform_id=*/0), 0u);
  EXPECT_EQ(QAdd(f, 5, /*job_id=*/2, /*inform_id=*/0), 0u);
  EXPECT_EQ(QFullValue(f, 5, "st"), 1u);  // at capacity
  EXPECT_EQ(QRemoveStatus(f, 5), 0u);
  EXPECT_EQ(QFullValue(f, 5, "st"), 0u);  // a slot has freed up
}

}  // namespace
