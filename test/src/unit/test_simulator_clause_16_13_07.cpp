#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.13.7: for a singly clocked sequence/property the local variable
// initialization assignment is performed when the evaluation attempt begins, and
// that attempt always begins at a tick of the single governing clock. The init
// time is therefore the attempt-begin time itself.
TEST(LocalVarInit, SinglyClockedInitsAtAttemptBegin) {
  EXPECT_EQ(SinglyClockedLocalInitTick(0), 0u);
  EXPECT_EQ(SinglyClockedLocalInitTick(20), 20u);

  // The attempt begins at a governing-clock tick, so the singly clocked init
  // coincides with the at-or-after reading when that tick is present.
  const std::vector<uint64_t> governing_ticks = {10, 20, 30};
  EXPECT_EQ(SinglyClockedLocalInitTick(20),
            MulticlockedLocalInitTick(/*attempt_begin=*/20, governing_ticks));
}

// §16.13.7: with a single semantic leading clock the init is performed at the
// earliest leading-clock tick at or after the attempt begin. A tick coincident
// with the begin qualifies.
TEST(LocalVarInit, SingleLeadingClockUsesEarliestTickAtOrAfter) {
  const std::vector<uint64_t> leading_ticks = {10, 20, 30};
  EXPECT_EQ(MulticlockedLocalInitTick(/*attempt_begin=*/20, leading_ticks), 20u);
  EXPECT_EQ(MulticlockedLocalInitTick(/*attempt_begin=*/13, leading_ticks), 20u);
  EXPECT_EQ(MulticlockedLocalInitTick(/*attempt_begin=*/0, leading_ticks), 10u);
}

// §16.13.7: when the semantic leading clock has no tick at or after the attempt
// begin there is nowhere to perform the init, signalled by the no-tick sentinel.
TEST(LocalVarInit, SingleLeadingClockWithNoFutureTickYieldsSentinel) {
  const std::vector<uint64_t> leading_ticks = {10, 20};
  EXPECT_EQ(MulticlockedLocalInitTick(/*attempt_begin=*/25, leading_ticks),
            kNoMulticlockTick);

  const std::vector<uint64_t> none = {};
  EXPECT_EQ(MulticlockedLocalInitTick(/*attempt_begin=*/0, none),
            kNoMulticlockTick);
}

// §16.13.7: a separate copy of the local variable is created for each distinct
// semantic leading clock of the instance — one copy for a single leading clock and
// two or more copies when there are two or more distinct leading clocks.
TEST(LocalVarInit, OneCopyPerDistinctSemanticLeadingClock) {
  EXPECT_EQ(LocalVarCopyCount(/*distinct_semantic_leading_clocks=*/1), 1u);
  EXPECT_EQ(LocalVarCopyCount(/*distinct_semantic_leading_clocks=*/2), 2u);
  EXPECT_EQ(LocalVarCopyCount(/*distinct_semantic_leading_clocks=*/3), 3u);
}

// §16.13.7: a single-leading-clock instance produces exactly one copy, whose init
// tick is the earliest leading-clock tick at or after the attempt begin.
TEST(LocalVarInit, SingleLeadingClockProducesOneCopy) {
  const std::vector<std::vector<uint64_t>> per_clock = {{5, 15, 25}};
  const std::vector<LocalVarInitCopy> copies =
      MulticlockedLocalInitCopies(/*attempt_begin=*/8, per_clock);
  ASSERT_EQ(copies.size(), 1u);
  EXPECT_EQ(copies[0].leading_clock_index, 0u);
  EXPECT_EQ(copies[0].init_tick, 15u);
}

// §16.13.7 example: `property p; logic v = e; (@(posedge clk1) ...) and
// (@(posedge clk2) ...)` instantiated under `@(posedge clk) f |=> p` has two
// semantic leading clocks (posedge clk1 and posedge clk2). A separate copy of v is
// created for each; each copy's init assignment is performed at the earliest tick
// of its own leading clock at or after the attempt begin, and that copy governs the
// subproperty associated with that leading clock.
TEST(LocalVarInit, TwoLeadingClocksGetIndependentlyScheduledCopies) {
  // Attempt begins strictly after t0 = 10; clk1 (index 0) next ticks at 14,
  // clk2 (index 1) next ticks at 17.
  const std::vector<std::vector<uint64_t>> per_clock = {
      {6, 14, 22},   // posedge clk1
      {9, 17, 25}};  // posedge clk2
  const std::vector<LocalVarInitCopy> copies =
      MulticlockedLocalInitCopies(/*attempt_begin=*/11, per_clock);

  ASSERT_EQ(copies.size(), 2u);
  EXPECT_EQ(copies[0].leading_clock_index, 0u);
  EXPECT_EQ(copies[0].init_tick, 14u);
  EXPECT_EQ(copies[1].leading_clock_index, 1u);
  EXPECT_EQ(copies[1].init_tick, 17u);

  // The two copies are scheduled independently — they need not share an init tick.
  EXPECT_NE(copies[0].init_tick, copies[1].init_tick);
}

// §16.13.7: each copy's schedule is governed solely by its own leading clock, so
// one copy may be unschedulable (no tick at or after the begin) while a sibling
// copy is initialized normally.
TEST(LocalVarInit, PerCopyScheduleIsIndependentAcrossLeadingClocks) {
  const std::vector<std::vector<uint64_t>> per_clock = {
      {10, 20, 30},  // has a tick at or after begin
      {2, 4}};       // exhausted before the begin
  const std::vector<LocalVarInitCopy> copies =
      MulticlockedLocalInitCopies(/*attempt_begin=*/12, per_clock);

  ASSERT_EQ(copies.size(), 2u);
  EXPECT_EQ(copies[0].init_tick, 20u);
  EXPECT_EQ(copies[1].init_tick, kNoMulticlockTick);
}

}  // namespace
