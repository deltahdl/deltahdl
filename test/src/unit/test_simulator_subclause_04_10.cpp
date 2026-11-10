#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

TEST(PliCallbackTaxonomy, RegisteredEvaluationCallbacksAreOneShot) {
  EXPECT_TRUE(IsOneShotPliCallback(kCbAfterDelay));
  EXPECT_TRUE(IsOneShotPliCallback(kCbNextSimTime));
  EXPECT_TRUE(IsOneShotPliCallback(kCbReadWriteSynch));
  EXPECT_TRUE(IsOneShotPliCallback(kCbAtStartOfSimTime));
  EXPECT_TRUE(IsOneShotPliCallback(kCbNBASynch));
  EXPECT_TRUE(IsOneShotPliCallback(kCbAtEndOfSimTime));
  EXPECT_TRUE(IsOneShotPliCallback(kCbReadOnlySynch));
}

TEST(PliCallbackTaxonomy, ValueChangeIsImmediate) {
  EXPECT_FALSE(IsOneShotPliCallback(kCbValueChange));
}

TEST(PliCallbackTaxonomy, UnknownReasonIsNotOneShot) {
  EXPECT_FALSE(IsOneShotPliCallback(0));
  EXPECT_FALSE(IsOneShotPliCallback(-1));
  EXPECT_FALSE(IsOneShotPliCallback(9999));
}

TEST(PliCallbackRegion, CbAfterDelayMapsToPreActive) {
  EXPECT_EQ(RegionForPliCallback(kCbAfterDelay), Region::kPreActive);
}

TEST(PliCallbackRegion, CbNextSimTimeMapsToPreActive) {
  EXPECT_EQ(RegionForPliCallback(kCbNextSimTime), Region::kPreActive);
}

TEST(PliCallbackRegion, CbAtStartOfSimTimeMapsToPreActive) {
  EXPECT_EQ(RegionForPliCallback(kCbAtStartOfSimTime), Region::kPreActive);
}

TEST(PliCallbackRegion, CbReadWriteSynchMapsToPreNbaOrPostNba) {
  Region r = RegionForPliCallback(kCbReadWriteSynch);
  EXPECT_TRUE(r == Region::kPreNBA || r == Region::kPostNBA)
      << "cbReadWriteSynch must map to Pre-NBA or Post-NBA per Table 4-1";
}

TEST(PliCallbackRegion, CbNbaSynchMapsToPreNba) {
  EXPECT_EQ(RegionForPliCallback(kCbNBASynch), Region::kPreNBA);
}

TEST(PliCallbackRegion, CbAtEndOfSimTimeMapsToPrePostponed) {
  EXPECT_EQ(RegionForPliCallback(kCbAtEndOfSimTime), Region::kPrePostponed);
}

TEST(PliCallbackRegion, CbReadOnlySynchMapsToPostponed) {
  EXPECT_EQ(RegionForPliCallback(kCbReadOnlySynch), Region::kPostponed);
}

TEST(PliCallbackRegion, NonOneShotCallbackHasNoAssignedRegion) {
  EXPECT_EQ(RegionForPliCallback(kCbValueChange), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(kCbStmt), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(kCbEndOfSimulation), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(0), Region::kCOUNT);
  EXPECT_EQ(RegionForPliCallback(9999), Region::kCOUNT);
}

TEST(PliCallbackConstants, OneShotCallbackReasonsAreDistinct) {
  EXPECT_NE(kCbAfterDelay, kCbNextSimTime);
  EXPECT_NE(kCbAfterDelay, kCbNBASynch);
  EXPECT_NE(kCbAfterDelay, kCbAtEndOfSimTime);
  EXPECT_NE(kCbNextSimTime, kCbNBASynch);
  EXPECT_NE(kCbNextSimTime, kCbAtEndOfSimTime);
  EXPECT_NE(kCbNBASynch, kCbAtEndOfSimTime);

  EXPECT_NE(kCbAfterDelay, kCbReadWriteSynch);
  EXPECT_NE(kCbAfterDelay, kCbAtStartOfSimTime);
  EXPECT_NE(kCbAfterDelay, kCbReadOnlySynch);
  EXPECT_NE(kCbAfterDelay, kCbValueChange);
}

namespace {

struct Sighting {
  std::string label;
  int q = 0;
  int r = 0;
  bool operator==(const Sighting&) const = default;
};

std::vector<Sighting>& Sightings() {
  static std::vector<Sighting> sightings;
  return sightings;
}

int IntOf(const char* name) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(vpi_handle_by_name(VpiText(name), nullptr), &value);
  return value.value.integer;
}

PLI_INT32 RecordSighting(p_cb_data cb) {
  Sightings().push_back({cb->user_data, IntOf("top.q"), IntOf("top.r")});
  return 0;
}

void PlaceAt(int reason, uint32_t delay, const char* label) {
  static s_vpi_time time;
  time.type = vpiSimTime;
  time.high = 0;
  time.low = delay;
  s_cb_data data = {};
  data.reason = reason;
  data.cb_rtn = &RecordSighting;
  data.time = &time;
  data.user_data = VpiText(label);
  vpi_register_cb(&data);
}

PLI_INT32 ArmOneShotCallbacks(p_cb_data) {
  PlaceAt(cbAfterDelay, 5, "after-delay");
  PlaceAt(cbAtStartOfSimTime, 5, "start-of-sim-time");
  PlaceAt(cbNBASynch, 5, "nba-synch");
  PlaceAt(cbReadWriteSynch, 5, "read-write-synch");
  PlaceAt(cbAtEndOfSimTime, 5, "end-of-sim-time");
  PlaceAt(cbReadOnlySynch, 5, "read-only-synch");
  return 0;
}

PLI_INT32 ArmValueChange(p_cb_data) {
  static s_vpi_time time;
  time.type = vpiSimTime;
  static s_vpi_value value;
  value.format = vpiIntVal;
  s_cb_data data = {};
  data.reason = cbValueChange;
  data.cb_rtn = &RecordSighting;
  data.obj = vpi_handle_by_name(VpiText("top.q"), nullptr);
  data.time = &time;
  data.value = &value;
  data.user_data = VpiText("q-changed");
  vpi_register_cb(&data);
  return 0;
}

class PliCallbacksOfARun : public VpiDesignRun {
 protected:
  void RunArmedBy(PLI_INT32 (*arm)(p_cb_data), const char* src) {
    Sightings().clear();
    s_cb_data data = {};
    data.reason = cbStartOfSimulation;
    data.cb_rtn = arm;
    ASSERT_NE(vpi_register_cb(&data), nullptr);
    Run(src);
  }
};

TEST_F(PliCallbacksOfARun, EachOneShotCallbackSeesTheSlotAtItsRegion) {
  RunArmedBy(&ArmOneShotCallbacks,
             "module top; timeunit 1ns; timeprecision 1ns; int q, r;\n"
             "  initial begin #5; q = 2; q <= 3; end\n"
             "endmodule\n");
  ASSERT_EQ(Sightings().size(), 6u);
  std::vector<Sighting> pre_active(Sightings().begin(),
                                   Sightings().begin() + 2);
  EXPECT_TRUE(pre_active ==
                  (std::vector<Sighting>{{"after-delay", 0, 0},
                                         {"start-of-sim-time", 0, 0}}) ||
              pre_active == (std::vector<Sighting>{{"start-of-sim-time", 0, 0},
                                                   {"after-delay", 0, 0}}));
  std::vector<Sighting> nba_side(Sightings().begin() + 2,
                                 Sightings().begin() + 4);
  EXPECT_TRUE(nba_side == (std::vector<Sighting>{{"nba-synch", 2, 0},
                                                 {"read-write-synch", 2, 0}}) ||
              nba_side == (std::vector<Sighting>{{"read-write-synch", 2, 0},
                                                 {"nba-synch", 2, 0}}) ||
              nba_side == (std::vector<Sighting>{{"nba-synch", 2, 0},
                                                 {"read-write-synch", 3, 0}}));
  EXPECT_EQ(Sightings()[4], (Sighting{"end-of-sim-time", 3, 0}));
  EXPECT_EQ(Sightings()[5], (Sighting{"read-only-synch", 3, 0}));
}

TEST_F(PliCallbacksOfARun, ValueChangeCallbackRunsAtOnceOnEachChange) {
  RunArmedBy(&ArmValueChange,
             "module top; timeunit 1ns; timeprecision 1ns; int q, r;\n"
             "  initial begin #1; q = 1; r = 10; q = 2; r = 20; end\n"
             "endmodule\n");
  EXPECT_EQ(Sightings(),
            (std::vector<Sighting>{{"q-changed", 1, 0}, {"q-changed", 2, 10}}));
}

}  // namespace
