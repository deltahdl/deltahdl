#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_stochastic_queue.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §20.15.6 Table 20-11, value 0: a well-formed $q_initialize reports OK.
TEST(StochasticQueueStatus, InitializeSucceedsWithOk) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 1, /*q_type=*/1, /*max_length=*/4), 0u);
}

// §20.15.6 Table 20-11, value 4: an unsupported q_type (only 1 and 2 are
// defined) fails creation with "unsupported queue type".
TEST(StochasticQueueStatus, UnsupportedQueueType) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 1, /*q_type=*/3, /*max_length=*/4), 4u);
}

// §20.15.6 Table 20-11, value 5: a zero max_length fails creation, exercising
// the boundary of the "length <= 0" condition.
TEST(StochasticQueueStatus, ZeroLength) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 1, /*q_type=*/2, /*max_length=*/0), 5u);
}

// §20.15.6 Table 20-11, value 5: a negative max_length also fails creation.
// This drives the signed interpretation of the length argument, so a value
// below zero is recognized rather than wrapping to a large positive capacity.
TEST(StochasticQueueStatus, NegativeLength) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 1, /*q_type=*/1, /*max_length=*/-4), 5u);
}

// §20.15.6 Table 20-11, value 6: re-using an existing q_id fails creation with
// "duplicate q_id".
TEST(StochasticQueueStatus, DuplicateQueueId) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 5, 1, 4), 0u);
  EXPECT_EQ(QInitialize(f, 5, 1, 4), 6u);
}

// §20.15.6 Table 20-11, value 2: adding to a q_id that was never created
// reports "undefined q_id".
TEST(StochasticQueueStatus, AddToUndefinedQueue) {
  SimFixture f;
  EXPECT_EQ(QAdd(f, 99), 2u);
}

// §20.15.6 Table 20-11, value 1: adding past the queue's capacity reports
// "queue full, cannot add". A successful add first returns OK.
TEST(StochasticQueueStatus, AddToFullQueue) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 1, 1, /*max_length=*/1), 0u);
  EXPECT_EQ(QAdd(f, 1), 0u);
  EXPECT_EQ(QAdd(f, 1), 1u);
}

// §20.15.6 Table 20-11, value 3: removing from an empty queue reports "queue
// empty, cannot remove"; a removed-then-emptied queue is detected across
// calls.
TEST(StochasticQueueStatus, RemoveFromEmptyQueue) {
  SimFixture f;
  EXPECT_EQ(QInitialize(f, 2, 1, 4), 0u);
  EXPECT_EQ(QRemoveStatus(f, 2), 3u);  // never added to
  EXPECT_EQ(QAdd(f, 2), 0u);
  EXPECT_EQ(QRemoveStatus(f, 2), 0u);  // drains the single entry
  EXPECT_EQ(QRemoveStatus(f, 2), 3u);  // now empty again
}

// §20.15.6 Table 20-11, value 2: $q_remove on an undefined q_id also reports
// "undefined q_id".
TEST(StochasticQueueStatus, RemoveFromUndefinedQueue) {
  SimFixture f;
  EXPECT_EQ(QRemoveStatus(f, 42), 2u);
}

// §20.15.6: $q_full returns a status code; an undefined q_id reports value 2,
// a live queue reports OK.
TEST(StochasticQueueStatus, FullReportsStatus) {
  SimFixture f;
  MakeVar(f, "st", 32, 0xDEAD);
  EXPECT_EQ(RunQueueCall(f, "$q_full", {MkInt(f.arena, 3), MkId(f.arena, "st")},
                         "st"),
            2u);
  EXPECT_EQ(QInitialize(f, 3, 1, 4), 0u);
  MakeVar(f, "st", 32, 0xDEAD);
  EXPECT_EQ(RunQueueCall(f, "$q_full", {MkInt(f.arena, 3), MkId(f.arena, "st")},
                         "st"),
            0u);
}

// §20.15.6: $q_exam returns a status code; an undefined q_id reports value 2,
// a live queue reports OK.
TEST(StochasticQueueStatus, ExamReportsStatus) {
  SimFixture f;
  MakeVar(f, "st", 32, 0xDEAD);
  EXPECT_EQ(RunQueueCall(f, "$q_exam",
                         {MkInt(f.arena, 8), MkInt(f.arena, 1),
                          MkInt(f.arena, 0), MkId(f.arena, "st")},
                         "st"),
            2u);
  EXPECT_EQ(QInitialize(f, 8, 2, 4), 0u);
  MakeVar(f, "st", 32, 0xDEAD);
  EXPECT_EQ(RunQueueCall(f, "$q_exam",
                         {MkInt(f.arena, 8), MkInt(f.arena, 1),
                          MkInt(f.arena, 0), MkId(f.arena, "st")},
                         "st"),
            0u);
}

}  // namespace
