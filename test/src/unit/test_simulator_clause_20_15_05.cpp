#include <cstdint>
#include <functional>
#include <vector>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §20.15.5 examines a queue's statistics through $q_exam's q_stat_value output,
// and several of those statistics (Table 20-10) depend on the simulation time
// at which entries are added and removed. These helpers run each queue
// task/function at whatever time the scheduler is currently at, so the tests
// can drive them from events placed at chosen times.

void Initialize(SimFixture& f, uint64_t q_id, int64_t q_type,
                int64_t max_length) {
  MakeVar(f, "st", 32, 0);
  auto* call = MkSysCall(
      f.arena, "$q_initialize",
      {MkInt(f.arena, q_id), MkInt(f.arena, static_cast<uint64_t>(q_type)),
       MkInt(f.arena, static_cast<uint64_t>(max_length)), MkId(f.arena, "st")});
  EvalExpr(call, f.ctx, f.arena);
}

void Add(SimFixture& f, uint64_t q_id) {
  MakeVar(f, "st", 32, 0);
  auto* call = MkSysCall(f.arena, "$q_add",
                         {MkInt(f.arena, q_id), MkInt(f.arena, 1),
                          MkInt(f.arena, 0), MkId(f.arena, "st")});
  EvalExpr(call, f.ctx, f.arena);
}

void Remove(SimFixture& f, uint64_t q_id) {
  MakeVar(f, "st", 32, 0);
  auto* call = MkSysCall(f.arena, "$q_remove",
                         {MkInt(f.arena, q_id), MkInt(f.arena, 0),
                          MkInt(f.arena, 0), MkId(f.arena, "st")});
  EvalExpr(call, f.ctx, f.arena);
}

// Run $q_exam for the requested q_stat_code and return the statistic delivered
// in the q_stat_value output argument.
uint64_t Exam(SimFixture& f, uint64_t q_id, uint64_t code) {
  MakeVar(f, "sv", 32, 0xDEAD);
  MakeVar(f, "st", 32, 0xDEAD);
  auto* call = MkSysCall(f.arena, "$q_exam",
                         {MkInt(f.arena, q_id), MkInt(f.arena, code),
                          MkId(f.arena, "sv"), MkId(f.arena, "st")});
  EvalExpr(call, f.ctx, f.arena);
  return f.ctx.FindVariable("sv")->value.ToUint64();
}

// Schedule `fn` to run at simulation time `t`. Inside the callback the
// scheduler's current time equals `t`, which is what the queue tasks stamp on
// arrivals and use to measure waits.
void At(SimFixture& f, uint64_t t, std::function<void()> fn) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = std::move(fn);
  f.scheduler.ScheduleEvent(SimTime{t}, Region::kActive, ev);
}

// §20.15.5 Table 20-10, code 1: the current queue length tracks live occupancy,
// rising with each add and falling with each remove.
TEST(QExam, CurrentQueueLength) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t after_two = 0, after_remove = 0;
  At(f, 0, [&] { Add(f, 1); });
  At(f, 1, [&] { Add(f, 1); });
  At(f, 2, [&] { after_two = Exam(f, 1, 1); });
  At(f, 3, [&] { Remove(f, 1); });
  At(f, 4, [&] { after_remove = Exam(f, 1, 1); });
  f.scheduler.Run();
  EXPECT_EQ(after_two, 2u);
  EXPECT_EQ(after_remove, 1u);
}

// §20.15.5 Table 20-10, code 3: the maximum queue length is the peak occupancy
// ever reached, retained even after entries drain back out.
TEST(QExam, MaximumQueueLength) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t peak = 0;
  At(f, 0, [&] { Add(f, 1); });
  At(f, 1, [&] { Add(f, 1); });
  At(f, 2, [&] { Add(f, 1); });  // occupancy peaks at 3 here
  At(f, 3, [&] { Remove(f, 1); });
  At(f, 4, [&] { Remove(f, 1); });
  At(f, 5, [&] { peak = Exam(f, 1, 3); });
  f.scheduler.Run();
  EXPECT_EQ(peak, 3u);
}

// §20.15.5 Table 20-10, code 2: the mean interarrival time is the average gap
// between successive arrivals: here arrivals at t=0, 4 and 10 give (10-0)/2
// = 5.
TEST(QExam, MeanInterarrivalTime) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t mean = 0;
  At(f, 0, [&] { Add(f, 1); });
  At(f, 4, [&] { Add(f, 1); });
  At(f, 10, [&] { Add(f, 1); });
  At(f, 11, [&] { mean = Exam(f, 1, 2); });
  f.scheduler.Run();
  EXPECT_EQ(mean, 5u);
}

// §20.15.5 Table 20-10, code 4: the shortest wait time ever is the smallest
// residence time across removed entries. FIFO removal drains the oldest entry
// first, so A waits 5 (0->5) and B waits 4 (2->6); the minimum is 4. Reporting
// the latest wait instead would give 4 only by coincidence, so the second
// remove is the shorter one to distinguish a true minimum from "most recent".
TEST(QExam, ShortestWaitEver) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t shortest = 0;
  At(f, 0, [&] { Add(f, 1); });     // entry A
  At(f, 2, [&] { Add(f, 1); });     // entry B
  At(f, 5, [&] { Remove(f, 1); });  // removes A, wait 5
  At(f, 6, [&] { Remove(f, 1); });  // removes B, wait 4
  At(f, 7, [&] { shortest = Exam(f, 1, 4); });
  f.scheduler.Run();
  EXPECT_EQ(shortest, 4u);
}

// §20.15.5 Table 20-10, code 6: the average wait time over removed entries.
// A waits 4 (0->4) and B waits 6 (4->10), averaging 5.
TEST(QExam, AverageWaitTime) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t average = 0;
  At(f, 0, [&] { Add(f, 1); });      // entry A
  At(f, 4, [&] { Remove(f, 1); });   // A waits 4
  At(f, 4, [&] { Add(f, 1); });      // entry B (same tick, after the remove)
  At(f, 10, [&] { Remove(f, 1); });  // B waits 6
  At(f, 11, [&] { average = Exam(f, 1, 6); });
  f.scheduler.Run();
  EXPECT_EQ(average, 5u);
}

// §20.15.5 Table 20-10, code 5: the longest wait among entries still in the
// queue is measured against the current time. The oldest still-present entry
// has waited the longest; once it is removed the next-oldest takes over.
TEST(QExam, LongestWaitStillQueued) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t with_oldest = 0, after_oldest_removed = 0;
  At(f, 0, [&] { Add(f, 1); });                              // entry A, oldest
  At(f, 3, [&] { Add(f, 1); });                              // entry B
  At(f, 10, [&] { with_oldest = Exam(f, 1, 5); });           // A waited 10
  At(f, 10, [&] { Remove(f, 1); });                          // remove A (FIFO)
  At(f, 10, [&] { after_oldest_removed = Exam(f, 1, 5); });  // now B, waited 7
  f.scheduler.Run();
  EXPECT_EQ(with_oldest, 10u);
  EXPECT_EQ(after_oldest_removed, 7u);
}

// §20.15.5: a q_stat_code outside the Table 20-10 range requests no defined
// statistic, so q_stat_value is left at zero.
TEST(QExam, UnknownStatCodeYieldsZero) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t value = 0xDEAD;
  At(f, 0, [&] { Add(f, 1); });
  At(f, 1, [&] { value = Exam(f, 1, /*code=*/99); });
  f.scheduler.Run();
  EXPECT_EQ(value, 0u);
}

// §20.15.5 Table 20-10, edge case: querying a queue that has never held an
// entry yields zero for occupancy-based statistics. Code 1 (current length)
// reports the empty count and code 5 (longest wait still queued) has no entry
// to measure, so both come back as zero.
TEST(QExam, StatisticsOnEmptyQueueAreZero) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t length = 0xDEAD, longest = 0xDEAD;
  At(f, 5, [&] { length = Exam(f, 1, 1); });
  At(f, 5, [&] { longest = Exam(f, 1, 5); });
  f.scheduler.Run();
  EXPECT_EQ(length, 0u);
  EXPECT_EQ(longest, 0u);
}

// §20.15.5 Table 20-10, edge case: the completed-wait statistics depend on
// entries having left the queue. With entries added but none yet removed, both
// the shortest wait ever (code 4) and the average wait (code 6) are zero.
TEST(QExam, WaitStatisticsBeforeAnyRemovalAreZero) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t shortest = 0xDEAD, average = 0xDEAD;
  At(f, 0, [&] { Add(f, 1); });
  At(f, 4, [&] { Add(f, 1); });
  At(f, 9, [&] { shortest = Exam(f, 1, 4); });
  At(f, 9, [&] { average = Exam(f, 1, 6); });
  f.scheduler.Run();
  EXPECT_EQ(shortest, 0u);
  EXPECT_EQ(average, 0u);
}

// §20.15.5 Table 20-10, edge case: the mean interarrival time (code 2) needs at
// least two arrivals to span a gap. A single arrival leaves no interval to
// average, so the result is zero.
TEST(QExam, MeanInterarrivalWithSingleArrivalIsZero) {
  SimFixture f;
  Initialize(f, 1, /*q_type=*/1, /*max_length=*/8);
  uint64_t mean = 0xDEAD;
  At(f, 3, [&] { Add(f, 1); });
  At(f, 7, [&] { mean = Exam(f, 1, 2); });
  f.scheduler.Run();
  EXPECT_EQ(mean, 0u);
}

}  // namespace
