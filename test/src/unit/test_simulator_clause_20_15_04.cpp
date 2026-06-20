#include "builders_systask.h"
#include "fixture_simulator.h"
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

uint64_t RunQueueCall(SimFixture& f, std::string_view name,
                      std::vector<Expr*> args, std::string_view status_name) {
  auto* call = MkSysCall(f.arena, name, std::move(args));
  EvalExpr(call, f.ctx, f.arena);
  return f.ctx.FindVariable(status_name)->value.ToUint64();
}

// $q_initialize(q_id, q_type, max_length, status): create the queue the
// fullness tests operate on, returning the creation status.
uint64_t Initialize(SimFixture& f, uint64_t q_id, int64_t q_type,
                    int64_t max_length) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(
      f, "$q_initialize",
      {MkInt(f.arena, q_id), MkInt(f.arena, static_cast<uint64_t>(q_type)),
       MkInt(f.arena, static_cast<uint64_t>(max_length)), MkId(f.arena, "st")},
      "st");
}

// $q_add(q_id, job_id, inform_id, status): place an entry onto queue q_id,
// returning the reported status.
uint64_t Add(SimFixture& f, uint64_t q_id, uint64_t job_id,
             uint64_t inform_id) {
  MakeVar(f, "st", 32, 0xDEAD);
  return RunQueueCall(f, "$q_add",
                      {MkInt(f.arena, q_id), MkInt(f.arena, job_id),
                       MkInt(f.arena, inform_id), MkId(f.arena, "st")},
                      "st");
}

// $q_full(q_id, status): evaluate the function and return its 0/1 fullness
// result. The status output is routed to a caller-named variable so it can be
// inspected separately when needed.
uint64_t Full(SimFixture& f, uint64_t q_id, std::string_view status_var) {
  MakeVar(f, status_var, 32, 0xDEAD);
  auto* call = MkSysCall(f.arena, "$q_full",
                         {MkInt(f.arena, q_id), MkId(f.arena, status_var)});
  return EvalExpr(call, f.ctx, f.arena).ToUint64();
}

// $q_remove(q_id, job_id, inform_id, status): take one entry off queue q_id
// (§20.15.3). The removed identifiers are routed to throwaway variables; only
// the resulting drop in occupancy matters to these fullness tests.
uint64_t Remove(SimFixture& f, uint64_t q_id) {
  MakeVar(f, "st", 32, 0xDEAD);
  MakeVar(f, "job", 32, 0);
  MakeVar(f, "inf", 32, 0);
  return RunQueueCall(f, "$q_remove",
                      {MkInt(f.arena, q_id), MkId(f.arena, "job"),
                       MkId(f.arena, "inf"), MkId(f.arena, "st")},
                      "st");
}

// §20.15.4: a freshly created queue holding no entries has room, so $q_full
// returns 0 (the queue is not full).
TEST(QFull, EmptyQueueIsNotFull) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 1, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(Full(f, 1, "st"), 0u);
}

// §20.15.4: a queue that holds fewer entries than its capacity still has room,
// so $q_full returns 0.
TEST(QFull, PartiallyFilledQueueIsNotFull) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 2, /*q_type=*/1, /*max_length=*/3), 0u);
  EXPECT_EQ(Add(f, 2, /*job_id=*/10, /*inform_id=*/0), 0u);
  EXPECT_EQ(Full(f, 2, "st"), 0u);
}

// §20.15.4: once the queue holds as many entries as its capacity allows, there
// is no room for another entry, so $q_full returns 1.
TEST(QFull, FullQueueReturnsOne) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 3, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(Add(f, 3, /*job_id=*/10, /*inform_id=*/0), 0u);
  EXPECT_EQ(Add(f, 3, /*job_id=*/20, /*inform_id=*/0), 0u);
  EXPECT_EQ(Full(f, 3, "st"), 1u);
}

// §20.15.4: a single-entry queue is full as soon as its one slot is occupied,
// confirming the result tracks capacity rather than a fixed threshold.
TEST(QFull, SingleEntryQueueIsFullAfterOneAdd) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 4, /*q_type=*/1, /*max_length=*/1), 0u);
  EXPECT_EQ(Full(f, 4, "st"), 0u);
  EXPECT_EQ(Add(f, 4, /*job_id=*/7, /*inform_id=*/0), 0u);
  EXPECT_EQ(Full(f, 4, "st"), 1u);
}

// §20.15.4: fullness reflects the queue's current occupancy, not a one-way
// latch. A queue filled to capacity reports full (1); after an entry is taken
// off it again has room, so $q_full reports not full (0).
TEST(QFull, ReportsNotFullAfterEntryRemoved) {
  SimFixture f;
  EXPECT_EQ(Initialize(f, 5, /*q_type=*/1, /*max_length=*/2), 0u);
  EXPECT_EQ(Add(f, 5, /*job_id=*/1, /*inform_id=*/0), 0u);
  EXPECT_EQ(Add(f, 5, /*job_id=*/2, /*inform_id=*/0), 0u);
  EXPECT_EQ(Full(f, 5, "st"), 1u);  // at capacity
  EXPECT_EQ(Remove(f, 5), 0u);
  EXPECT_EQ(Full(f, 5, "st"), 0u);  // a slot has freed up
}

}  // namespace
