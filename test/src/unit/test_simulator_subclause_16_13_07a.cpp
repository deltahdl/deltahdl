#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulator/sva_engine_properties.h"

using namespace delta;

namespace {

TEST(LocalVarInit, SinglyClockedInitsAtAttemptBegin) {
  EXPECT_EQ(SinglyClockedLocalInitTick(0), 0u);
  EXPECT_EQ(SinglyClockedLocalInitTick(20), 20u);

  const std::vector<uint64_t> kGoverningTicks = {10, 20, 30};
  EXPECT_EQ(SinglyClockedLocalInitTick(20),
            MulticlockedLocalInitTick(20, kGoverningTicks));
}

TEST(LocalVarInit, SingleLeadingClockUsesEarliestTickAtOrAfter) {
  const std::vector<uint64_t> kLeadingTicks = {10, 20, 30};
  EXPECT_EQ(MulticlockedLocalInitTick(20, kLeadingTicks), 20u);
  EXPECT_EQ(MulticlockedLocalInitTick(13, kLeadingTicks), 20u);
  EXPECT_EQ(MulticlockedLocalInitTick(0, kLeadingTicks), 10u);
}

TEST(LocalVarInit, SingleLeadingClockWithNoFutureTickYieldsSentinel) {
  const std::vector<uint64_t> kLeadingTicks = {10, 20};
  EXPECT_EQ(MulticlockedLocalInitTick(25, kLeadingTicks), kNoMulticlockTick);

  const std::vector<uint64_t> kNone = {};
  EXPECT_EQ(MulticlockedLocalInitTick(0, kNone), kNoMulticlockTick);
}

TEST(LocalVarInit, OneCopyPerDistinctSemanticLeadingClock) {
  EXPECT_EQ(LocalVarCopyCount(1), 1u);
  EXPECT_EQ(LocalVarCopyCount(2), 2u);
  EXPECT_EQ(LocalVarCopyCount(3), 3u);
}

TEST(LocalVarInit, TwoLeadingClocksGetIndependentlyScheduledCopies) {
  const std::vector<std::vector<uint64_t>> kPerClock = {{6, 14, 22},
                                                        {9, 17, 25}};
  const std::vector<LocalVarInitCopy> kCopies =
      MulticlockedLocalInitCopies(11, kPerClock);

  ASSERT_EQ(kCopies.size(), 2u);
  EXPECT_EQ(kCopies[0].leading_clock_index, 0u);
  EXPECT_EQ(kCopies[0].init_tick, 14u);
  EXPECT_EQ(kCopies[1].leading_clock_index, 1u);
  EXPECT_EQ(kCopies[1].init_tick, 17u);

  EXPECT_NE(kCopies[0].init_tick, kCopies[1].init_tick);
}

TEST(LocalVarInit, PerCopyScheduleIsIndependentAcrossLeadingClocks) {
  const std::vector<std::vector<uint64_t>> kPerClock = {{10, 20, 30}, {2, 4}};
  const std::vector<LocalVarInitCopy> kCopies =
      MulticlockedLocalInitCopies(12, kPerClock);

  ASSERT_EQ(kCopies.size(), 2u);
  EXPECT_EQ(kCopies[0].init_tick, 20u);
  EXPECT_EQ(kCopies[1].init_tick, kNoMulticlockTick);
}

}  // namespace
