#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_scheduler_event.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(PliRegionSim, PLIRegionEnumsExist) {
  auto preponed = static_cast<int>(Region::kPreponed);
  auto pre_active = static_cast<int>(Region::kPreActive);
  auto pre_nba = static_cast<int>(Region::kPreNBA);
  auto post_nba = static_cast<int>(Region::kPostNBA);
  auto pre_observed = static_cast<int>(Region::kPreObserved);
  auto post_observed = static_cast<int>(Region::kPostObserved);
  auto pre_renba = static_cast<int>(Region::kPreReNBA);
  auto post_renba = static_cast<int>(Region::kPostReNBA);
  auto pre_postponed = static_cast<int>(Region::kPrePostponed);

  std::vector<int> ordinals = {preponed,  pre_active,   pre_nba,
                               post_nba,  pre_observed, post_observed,
                               pre_renba, post_renba,   pre_postponed};
  for (size_t i = 0; i < ordinals.size(); ++i) {
    for (size_t j = i + 1; j < ordinals.size(); ++j) {
      EXPECT_NE(ordinals[i], ordinals[j]);
    }
  }
}

TEST(PliRegionSim, ExactlyNinePLIRegionsExist) {
  std::vector<Region> pli_regions = {
      Region::kPreponed, Region::kPreActive,   Region::kPreNBA,
      Region::kPostNBA,  Region::kPreObserved, Region::kPostObserved,
      Region::kPreReNBA, Region::kPostReNBA,   Region::kPrePostponed};
  EXPECT_EQ(pli_regions.size(), 9u);

  for (auto r : pli_regions) {
    EXPECT_LT(static_cast<int>(r), static_cast<int>(Region::kCOUNT));
  }
}

TEST(PliRegionSim, PLIRegionsAreInterleavedWithSimulationRegions) {
  EXPECT_LT(static_cast<int>(Region::kPreActive),
            static_cast<int>(Region::kActive));
  EXPECT_LT(static_cast<int>(Region::kPreNBA), static_cast<int>(Region::kNBA));
  EXPECT_LT(static_cast<int>(Region::kPreObserved),
            static_cast<int>(Region::kObserved));
  EXPECT_LT(static_cast<int>(Region::kPreReNBA),
            static_cast<int>(Region::kReNBA));
  EXPECT_LT(static_cast<int>(Region::kPrePostponed),
            static_cast<int>(Region::kPostponed));

  EXPECT_GT(static_cast<int>(Region::kPostNBA), static_cast<int>(Region::kNBA));
  EXPECT_GT(static_cast<int>(Region::kPostObserved),
            static_cast<int>(Region::kObserved));
  EXPECT_GT(static_cast<int>(Region::kPostReNBA),
            static_cast<int>(Region::kReNBA));
}

TEST(PliRegionSim, PreActiveExecutesBetweenPreponedAndActive) {
  VerifyThreeRegionOrder({Region::kPreponed, "preponed"},
                         {Region::kPreActive, "pre_active"},
                         {Region::kActive, "active"});
}

TEST(PliRegionSim, PreNBAExecutesBetweenInactiveAndNBA) {
  VerifyThreeRegionOrder({Region::kInactive, "inactive"},
                         {Region::kPreNBA, "pre_nba"}, {Region::kNBA, "nba"});
}

TEST(PliRegionSim, PostNBAExecutesAfterNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostNBA, "post_nba", order);
  ScheduleLabeled(sched, Region::kNBA, "nba", order);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "nba");
  EXPECT_EQ(order[1], "post_nba");
}

TEST(PliRegionSim, PreObservedExecutesBetweenPostNBAAndObserved) {
  VerifyThreeRegionOrder({Region::kPostNBA, "post_nba"},
                         {Region::kPreObserved, "pre_observed"},
                         {Region::kObserved, "observed"});
}

TEST(PliRegionSim, PreReNBAExecutesBetweenReInactiveAndReNBA) {
  VerifyThreeRegionOrder({Region::kReInactive, "reinactive"},
                         {Region::kPreReNBA, "pre_renba"},
                         {Region::kReNBA, "renba"});
}

TEST(PliRegionSim, PostReNBAExecutesBetweenReNBAAndPrePostponed) {
  VerifyThreeRegionOrder({Region::kReNBA, "renba"},
                         {Region::kPostReNBA, "post_renba"},
                         {Region::kPrePostponed, "pre_postponed"});
}

TEST(PliRegionSim, PrePostponedExecutesBeforePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, Region::kPostponed, "postponed", order);
  ScheduleLabeled(sched, Region::kPrePostponed, "pre_postponed", order);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_postponed");
  EXPECT_EQ(order[1], "postponed");
}

TEST(PliRegionSim, FullPLIRegionOrderingPerFigure41) { VerifyAllRegionOrder(); }

TEST(PliRegionSim, PLIRegionsExecuteAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  ScheduleLabeled(sched, 0, Region::kPreActive, "t0_pre_active", order);
  ScheduleLabeled(sched, 0, Region::kActive, "t0_active", order);

  ScheduleLabeled(sched, 1, Region::kPreNBA, "t1_pre_nba", order);
  ScheduleLabeled(sched, 1, Region::kNBA, "t1_nba", order);

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "t0_pre_active");
  EXPECT_EQ(order[1], "t0_active");
  EXPECT_EQ(order[2], "t1_pre_nba");
  EXPECT_EQ(order[3], "t1_nba");
}

TEST(PliRegionSim, PLICallbackSchedulesIntoSimulationRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* pli_ev = sched.GetEventPool().Acquire();
  pli_ev->callback = [&]() {
    order.push_back("pre_active");
    auto* active_ev = sched.GetEventPool().Acquire();
    active_ev->callback = [&order]() { order.push_back("active_from_pli"); };
    sched.ScheduleEvent({0}, Region::kActive, active_ev);
  };
  sched.ScheduleEvent({0}, Region::kPreActive, pli_ev);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_active");
  EXPECT_EQ(order[1], "active_from_pli");
}
