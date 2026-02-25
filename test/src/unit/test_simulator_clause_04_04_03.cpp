#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

// ===========================================================================
// §4.4.3 PLI regions
//
// Figure 4-1 PLI region edges (DOT GraphViz at ~/Figure_4_1.gv):
//   region_Preponed    -> pli_region_PreActive        (line 53)
//   pli_region_PreActive -> region_Active              (line 36)
//   region_Inactive    -> pli_region_PreNBA            (line 46)
//   pli_region_PreNBA  -> region_NBA                   (line 38)
//   pli_region_PreNBA  -> region_Active                (line 37)
//   region_NBA         -> pli_region_PostNBA           (line 48)
//   pli_region_PostNBA -> pli_region_PreObserved       (line 29)
//   pli_region_PostNBA -> region_Active                (line 30)
//   pli_region_PreObserved -> region_Observed          (line 39)
//   region_Observed    -> pli_region_PostObserved      (line 50)
//   pli_region_PostObserved -> region_Reactive         (line 32)
//   pli_region_PostObserved -> region_Active           (line 31)
//   region_ReInactive  -> pli_region_PreReNBA          (line 56)
//   pli_region_PreReNBA -> region_ReNBA                (line 42)
//   pli_region_PreReNBA -> region_Reactive             (line 43)
//   region_ReNBA       -> pli_region_PostReNBA         (line 58)
//   pli_region_PostReNBA -> pli_region_PrePostponed    (line 33)
//   pli_region_PostReNBA -> region_Active              (line 34)
//   pli_region_PostReNBA -> region_Reactive            (line 35)
//   pli_region_PrePostponed -> region_Postponed        (line 41)
//   pli_region_PrePostponed -> region_Active           (line 40)
//
// The PLI regions are interleaved with the simulation regions per §4.4.2.
// ===========================================================================

// ---------------------------------------------------------------------------
// §4.4.3 PLI-specific regions
// All 9 PLI region enum values exist and are distinct from each other.
// ---------------------------------------------------------------------------
TEST(SimCh443, PLIRegionEnumsExist) {
  auto preponed = static_cast<int>(Region::kPreponed);
  auto pre_active = static_cast<int>(Region::kPreActive);
  auto pre_nba = static_cast<int>(Region::kPreNBA);
  auto post_nba = static_cast<int>(Region::kPostNBA);
  auto pre_observed = static_cast<int>(Region::kPreObserved);
  auto post_observed = static_cast<int>(Region::kPostObserved);
  auto pre_renba = static_cast<int>(Region::kPreReNBA);
  auto post_renba = static_cast<int>(Region::kPostReNBA);
  auto pre_postponed = static_cast<int>(Region::kPrePostponed);

  // All 9 PLI regions have distinct ordinals.
  std::vector<int> ordinals = {preponed,  pre_active,   pre_nba,
                               post_nba,  pre_observed, post_observed,
                               pre_renba, post_renba,   pre_postponed};
  for (size_t i = 0; i < ordinals.size(); ++i) {
    for (size_t j = i + 1; j < ordinals.size(); ++j) {
      EXPECT_NE(ordinals[i], ordinals[j]);
    }
  }
}

// ---------------------------------------------------------------------------
// §4.4.3 PLI regions of a time slot
// There are exactly 9 PLI regions.  They are a subset of the full region
// enum (which also includes simulation regions).
// ---------------------------------------------------------------------------
TEST(SimCh443, ExactlyNinePLIRegionsExist) {
  // The 9 PLI regions enumerated by the LRM.
  std::vector<Region> pli_regions = {
      Region::kPreponed, Region::kPreActive,   Region::kPreNBA,
      Region::kPostNBA,  Region::kPreObserved, Region::kPostObserved,
      Region::kPreReNBA, Region::kPostReNBA,   Region::kPrePostponed};
  EXPECT_EQ(pli_regions.size(), 9u);

  // Each PLI region ordinal is within [0, kCOUNT).
  for (auto r : pli_regions) {
    EXPECT_LT(static_cast<int>(r), static_cast<int>(Region::kCOUNT));
  }
}

// ---------------------------------------------------------------------------
// §4.4.3 PLI regions interleaved with simulation regions
// PLI regions are interleaved with simulation regions: each PLI region's
// ordinal sits between its neighboring simulation regions.
// ---------------------------------------------------------------------------
TEST(SimCh443, PLIRegionsAreInterleavedWithSimulationRegions) {
  // PLI "Pre-" regions precede their associated simulation region.
  EXPECT_LT(static_cast<int>(Region::kPreActive),
            static_cast<int>(Region::kActive));
  EXPECT_LT(static_cast<int>(Region::kPreNBA), static_cast<int>(Region::kNBA));
  EXPECT_LT(static_cast<int>(Region::kPreObserved),
            static_cast<int>(Region::kObserved));
  EXPECT_LT(static_cast<int>(Region::kPreReNBA),
            static_cast<int>(Region::kReNBA));
  EXPECT_LT(static_cast<int>(Region::kPrePostponed),
            static_cast<int>(Region::kPostponed));

  // PLI "Post-" regions follow their associated simulation region.
  EXPECT_GT(static_cast<int>(Region::kPostNBA), static_cast<int>(Region::kNBA));
  EXPECT_GT(static_cast<int>(Region::kPostObserved),
            static_cast<int>(Region::kObserved));
  EXPECT_GT(static_cast<int>(Region::kPostReNBA),
            static_cast<int>(Region::kReNBA));
}

// ---------------------------------------------------------------------------
// §4.4.3 PLI region execution flow per Figure 4-1
// Figure 4-1: region_Preponed -> pli_region_PreActive -> region_Active.
// Pre-Active PLI region executes between Preponed and Active.
// ---------------------------------------------------------------------------
TEST(SimCh443, PreActiveExecutesBetweenPreponedAndActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kActive, "active");
  schedule(Region::kPreActive, "pre_active");
  schedule(Region::kPreponed, "preponed");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "preponed");
  EXPECT_EQ(order[1], "pre_active");
  EXPECT_EQ(order[2], "active");
}

// ---------------------------------------------------------------------------
// §4.4.3 Figure 4-1: region_Inactive -> pli_region_PreNBA -> region_NBA.
// Pre-NBA PLI region executes between Inactive and NBA.
// ---------------------------------------------------------------------------
TEST(SimCh443, PreNBAExecutesBetweenInactiveAndNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kNBA, "nba");
  schedule(Region::kPreNBA, "pre_nba");
  schedule(Region::kInactive, "inactive");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "inactive");
  EXPECT_EQ(order[1], "pre_nba");
  EXPECT_EQ(order[2], "nba");
}

// ---------------------------------------------------------------------------
// §4.4.3 Figure 4-1: region_NBA -> pli_region_PostNBA -> ...
// Post-NBA PLI region executes after NBA.
// ---------------------------------------------------------------------------
TEST(SimCh443, PostNBAExecutesAfterNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kPostNBA, "post_nba");
  schedule(Region::kNBA, "nba");

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "nba");
  EXPECT_EQ(order[1], "post_nba");
}

// ---------------------------------------------------------------------------
// §4.4.3 Figure 4-1: pli_region_PostNBA -> pli_region_PreObserved ->
// region_Observed.
// Pre-Observed PLI region executes between Post-NBA and Observed.
// ---------------------------------------------------------------------------
TEST(SimCh443, PreObservedExecutesBetweenPostNBAAndObserved) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kObserved, "observed");
  schedule(Region::kPreObserved, "pre_observed");
  schedule(Region::kPostNBA, "post_nba");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "post_nba");
  EXPECT_EQ(order[1], "pre_observed");
  EXPECT_EQ(order[2], "observed");
}

// ---------------------------------------------------------------------------
// §4.4.3 Figure 4-1: region_Observed -> pli_region_PostObserved ->
// region_Reactive.
// Post-Observed PLI region executes between Observed and Reactive.
// ---------------------------------------------------------------------------
TEST(SimCh443, PostObservedExecutesBetweenObservedAndReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kReactive, "reactive");
  schedule(Region::kPostObserved, "post_observed");
  schedule(Region::kObserved, "observed");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "observed");
  EXPECT_EQ(order[1], "post_observed");
  EXPECT_EQ(order[2], "reactive");
}

// ---------------------------------------------------------------------------
// §4.4.3 Figure 4-1: region_ReInactive -> pli_region_PreReNBA ->
// region_ReNBA.
// Pre-Re-NBA PLI region executes between Re-Inactive and Re-NBA.
// ---------------------------------------------------------------------------
TEST(SimCh443, PreReNBAExecutesBetweenReInactiveAndReNBA) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kReNBA, "renba");
  schedule(Region::kPreReNBA, "pre_renba");
  schedule(Region::kReInactive, "reinactive");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "reinactive");
  EXPECT_EQ(order[1], "pre_renba");
  EXPECT_EQ(order[2], "renba");
}

// ---------------------------------------------------------------------------
// §4.4.3 Figure 4-1: region_ReNBA -> pli_region_PostReNBA ->
// pli_region_PrePostponed.
// Post-Re-NBA PLI region executes between Re-NBA and Pre-Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh443, PostReNBAExecutesBetweenReNBAAndPrePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kPrePostponed, "pre_postponed");
  schedule(Region::kPostReNBA, "post_renba");
  schedule(Region::kReNBA, "renba");

  sched.Run();
  ASSERT_EQ(order.size(), 3u);
  EXPECT_EQ(order[0], "renba");
  EXPECT_EQ(order[1], "post_renba");
  EXPECT_EQ(order[2], "pre_postponed");
}

// ---------------------------------------------------------------------------
// §4.4.3 Figure 4-1: pli_region_PrePostponed -> region_Postponed.
// Pre-Postponed PLI region executes before Postponed.
// ---------------------------------------------------------------------------
TEST(SimCh443, PrePostponedExecutesBeforePostponed) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  schedule(Region::kPostponed, "postponed");
  schedule(Region::kPrePostponed, "pre_postponed");

  sched.Run();
  ASSERT_EQ(order.size(), 2u);
  EXPECT_EQ(order[0], "pre_postponed");
  EXPECT_EQ(order[1], "postponed");
}

// ---------------------------------------------------------------------------
// §4.4.3 Full PLI region ordering per Figure 4-1
// Full PLI region ordering: all 9 PLI regions execute in their specified
// positions relative to each other and the simulation regions.
// ---------------------------------------------------------------------------
TEST(SimCh443, FullPLIRegionOrderingPerFigure41) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({0}, r, ev);
  };

  // Schedule all regions in reverse order to prove ordering is structural.
  schedule(Region::kPostponed, "postponed");
  schedule(Region::kPrePostponed, "pre_postponed");
  schedule(Region::kPostReNBA, "post_renba");
  schedule(Region::kReNBA, "renba");
  schedule(Region::kPreReNBA, "pre_renba");
  schedule(Region::kReInactive, "reinactive");
  schedule(Region::kReactive, "reactive");
  schedule(Region::kPostObserved, "post_observed");
  schedule(Region::kObserved, "observed");
  schedule(Region::kPreObserved, "pre_observed");
  schedule(Region::kPostNBA, "post_nba");
  schedule(Region::kNBA, "nba");
  schedule(Region::kPreNBA, "pre_nba");
  schedule(Region::kInactive, "inactive");
  schedule(Region::kActive, "active");
  schedule(Region::kPreActive, "pre_active");
  schedule(Region::kPreponed, "preponed");

  sched.Run();
  std::vector<std::string> expected = {
      "preponed",  "pre_active",    "active",     "inactive",
      "pre_nba",   "nba",           "post_nba",   "pre_observed",
      "observed",  "post_observed", "reactive",   "reinactive",
      "pre_renba", "renba",         "post_renba", "pre_postponed",
      "postponed"};
  EXPECT_EQ(order, expected);
}

// ---------------------------------------------------------------------------
// §4.4.3 PLI regions execute in their respective positions across multiple
// time slots, verifying the flow is per-time-slot as specified.
// ---------------------------------------------------------------------------
TEST(SimCh443, PLIRegionsExecuteAcrossMultipleTimeSlots) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto schedule = [&](uint64_t t, Region r, const std::string& label) {
    auto* ev = sched.GetEventPool().Acquire();
    ev->callback = [&order, label]() { order.push_back(label); };
    sched.ScheduleEvent({t}, r, ev);
  };

  // Time 0: Pre-Active and Active
  schedule(0, Region::kPreActive, "t0_pre_active");
  schedule(0, Region::kActive, "t0_active");

  // Time 1: Pre-NBA and NBA
  schedule(1, Region::kPreNBA, "t1_pre_nba");
  schedule(1, Region::kNBA, "t1_nba");

  sched.Run();
  ASSERT_EQ(order.size(), 4u);
  EXPECT_EQ(order[0], "t0_pre_active");
  EXPECT_EQ(order[1], "t0_active");
  EXPECT_EQ(order[2], "t1_pre_nba");
  EXPECT_EQ(order[3], "t1_nba");
}

// ---------------------------------------------------------------------------
// §4.4.3 PLI callbacks scheduling into simulation regions
// PLI regions can schedule events -- a PLI callback (Pre-Active) schedules
// into the Active simulation region, as Figure 4-1 shows:
// pli_region_PreActive -> region_Active.
// ---------------------------------------------------------------------------
TEST(SimCh443, PLICallbackSchedulesIntoSimulationRegion) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  // Pre-Active callback schedules an Active event.
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
