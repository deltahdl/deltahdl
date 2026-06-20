#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// Drive a queue task/function through the evaluator and report the value left
// in its trailing `status` output argument. §20.15.6 requires every queue
// management task and function to return such an output status code.
uint64_t RunQueueCall(SimFixture& f, std::string_view name,
                      std::vector<Expr*> args, std::string_view status_name) {
  auto* call = MkSysCall(f.arena, name, std::move(args));
  EvalExpr(call, f.ctx, f.arena);
  return f.ctx.FindVariable(status_name)->value.ToUint64();
}

// Create a queue with the given type/length, returning the status the
// creation reported. Pre-seeds a fresh `status` variable each time.
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

// §20.15.6 Table 20-11, value 0: a well-formed $q_initialize reports OK.
TEST(StochasticQueueStatus, InitializeSucceedsWithOk) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, /*q_type=*/1, /*max_length=*/4), 0u);
}

// §20.15.6 Table 20-11, value 4: an unsupported q_type (only 1 and 2 are
// defined) fails creation with "unsupported queue type".
TEST(StochasticQueueStatus, UnsupportedQueueType) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, /*q_type=*/3, /*max_length=*/4), 4u);
}

// §20.15.6 Table 20-11, value 5: a zero max_length fails creation, exercising
// the boundary of the "length <= 0" condition.
TEST(StochasticQueueStatus, ZeroLength) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, /*q_type=*/2, /*max_length=*/0), 5u);
}

// §20.15.6 Table 20-11, value 5: a negative max_length also fails creation.
// This drives the signed interpretation of the length argument, so a value
// below zero is recognized rather than wrapping to a large positive capacity.
TEST(StochasticQueueStatus, NegativeLength) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, /*q_type=*/1, /*max_length=*/-4), 5u);
}

// §20.15.6 Table 20-11, value 6: re-using an existing q_id fails creation with
// "duplicate q_id".
TEST(StochasticQueueStatus, DuplicateQueueId) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 5, 1, 4), 0u);
  EXPECT_EQ(Initialize(f, 5, 1, 4), 6u);
}

// §20.15.6 Table 20-11, value 2: adding to a q_id that was never created
// reports "undefined q_id".
TEST(StochasticQueueStatus, AddToUndefinedQueue) {
  SimFixture f;
  EXPECT_EQ(Add(f, 99), 2u);
}

// §20.15.6 Table 20-11, value 1: adding past the queue's capacity reports
// "queue full, cannot add". A successful add first returns OK.
TEST(StochasticQueueStatus, AddToFullQueue) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, 1, /*max_length=*/1), 0u);
  EXPECT_EQ(Add(f, 1), 0u);
  EXPECT_EQ(Add(f, 1), 1u);
}

// §20.15.6 Table 20-11, value 3: removing from an empty queue reports "queue
// empty, cannot remove"; a removed-then-emptied queue is detected across
// calls.
TEST(StochasticQueueStatus, RemoveFromEmptyQueue) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 2, 1, 4), 0u);
  EXPECT_EQ(Remove(f, 2), 3u);  // never added to
  EXPECT_EQ(Add(f, 2), 0u);
  EXPECT_EQ(Remove(f, 2), 0u);  // drains the single entry
  EXPECT_EQ(Remove(f, 2), 3u);  // now empty again
}

// §20.15.6 Table 20-11, value 2: $q_remove on an undefined q_id also reports
// "undefined q_id".
TEST(StochasticQueueStatus, RemoveFromUndefinedQueue) {
  SimFixture f;
  EXPECT_EQ(Remove(f, 42), 2u);
}

// §20.15.6: $q_full returns a status code; an undefined q_id reports value 2,
// a live queue reports OK.
TEST(StochasticQueueStatus, FullReportsStatus) {
  SimFixture f;
  MakeVar(f, "st", 32, 0xDEAD);
  EXPECT_EQ(RunQueueCall(f, "$q_full", {MkInt(f.arena, 3), MkId(f.arena, "st")},
                         "st"),
            2u);
  EXPECT_EQ(Initialize(f, 3, 1, 4), 0u);
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
  EXPECT_EQ(Initialize(f, 8, 2, 4), 0u);
  MakeVar(f, "st", 32, 0xDEAD);
  EXPECT_EQ(RunQueueCall(f, "$q_exam",
                         {MkInt(f.arena, 8), MkInt(f.arena, 1),
                          MkInt(f.arena, 0), MkId(f.arena, "st")},
                         "st"),
            0u);
}

}  // namespace
