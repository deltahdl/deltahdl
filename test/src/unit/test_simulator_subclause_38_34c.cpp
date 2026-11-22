#include <gtest/gtest.h>

#include <vector>

#include "helpers_vpi_put_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct TimedPutResults {
  std::vector<int> read_at_once;
  std::vector<vpiHandle> returned;
  std::vector<int> changes;
  vpiHandle event = nullptr;
  PLI_INT32 scheduled = -1;
  PLI_INT32 error = -1;
  PLI_INT32 released = -1;
  PLI_INT32 type = 0;
};

TimedPutResults results;

constexpr const char* kSampledAt3And5 =
    "module top; timeunit 1ns; timeprecision 1ns; int v, v_at3, v_at5;\n"
    "  initial begin #1 $put; #2 v_at3 = v; #2 v_at5 = v; end\n"
    "endmodule\n";

PLI_INT32 RecordChange(s_cb_data* data) {
  results.changes.push_back(data->value->value.integer);
  return 0;
}

class TimedPutsOfARun : public VpiPutRun {
 protected:
  void SetUp() override {
    VpiPutRun::SetUp();
    results = {};
  }

  static void WatchChangesOf(const char* name) {
    static s_vpi_time time = {vpiSuppressTime, 0, 0, 0.0};
    static s_vpi_value value = {vpiIntVal, {}};
    s_cb_data cb = {};
    cb.reason = cbValueChange;
    cb.cb_rtn = &RecordChange;
    cb.obj = vpi_handle_by_name(VpiText(name), nullptr);
    cb.time = &time;
    cb.value = &value;
    vpi_register_cb(&cb);
  }
};

TEST_F(TimedPutsOfARun, ANoDelayPutIgnoresAnyTimeAndWritesAtOnce) {
  Putter() = [] {
    s_vpi_time low = {vpiSimTime, 0, 10, 0.0};
    s_vpi_time high = {vpiSimTime, 1, 0, 0.0};
    s_vpi_time real = {vpiScaledRealTime, 0, 0, 4.0};
    const char* const kNames[] = {"top.a", "top.b", "top.c"};
    s_vpi_time* const kTimes[] = {&low, &high, &real};
    for (int i = 0; i < 3; ++i) {
      results.returned.push_back(
          PutIntAt(kNames[i], 5 + i, vpiNoDelay | vpiReturnEvent, kTimes[i]));
      results.read_at_once.push_back(IntOf(kNames[i]));
    }
  };
  Run("module top; int a, b, c; initial #1 $put; endmodule\n");
  EXPECT_EQ(results.read_at_once, (std::vector<int>{5, 6, 7}));
  EXPECT_EQ(results.returned,
            (std::vector<vpiHandle>{nullptr, nullptr, nullptr}));
}

TEST_F(TimedPutsOfARun, ATransportPutKeepsAnEventDueAtTheSameTime) {
  Putter() = [] {
    WatchChangesOf("top.v");
    PutInt("top.v", 6, vpiTransportDelay, 3);
    PutInt("top.v", 7, vpiTransportDelay, 3);
  };
  Run(kSampledAt3And5);
  EXPECT_EQ(results.changes, (std::vector<int>{6, 7}));
  EXPECT_EQ(IntOf("top.v_at5"), 7);
}

TEST_F(TimedPutsOfARun, ATransportPutLeavesAnotherObjectsEventsAlone) {
  Putter() = [] {
    PutInt("top.v", 6, vpiTransportDelay, 3);
    PutInt("top.w", 7, vpiTransportDelay, 1);
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; int v, w, v_at5;\n"
      "  initial begin #1 $put; #4 v_at5 = v; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.v_at5"), 6);
  EXPECT_EQ(IntOf("top.w"), 7);
}

TEST_F(TimedPutsOfARun, ReleasingAnEventHandleLeavesTheEventScheduled) {
  Putter() = [] {
    vpiHandle event = PutInt("top.v", 6, vpiTransportDelay | vpiReturnEvent, 3);
    results.released = vpi_release_handle(event);
  };
  Run(kSampledAt3And5);
  EXPECT_EQ(results.released, 1);
  EXPECT_EQ(IntOf("top.v_at3"), 0);
  EXPECT_EQ(IntOf("top.v_at5"), 6);
}

TEST_F(TimedPutsOfARun, ACancelFreesTheEventsHandle) {
  Putter() = [] {
    vpiHandle event = PutInt("top.v", 6, vpiTransportDelay | vpiReturnEvent, 3);
    vpi_put_value(event, nullptr, nullptr, vpiCancelEvent);
    results.released = vpi_release_handle(event);
  };
  Run(kSampledAt3And5);
  EXPECT_EQ(results.released, 0);
  EXPECT_EQ(IntOf("top.v_at5"), 0);
}

TEST_F(TimedPutsOfARun, DISABLED_ARefusedDelayedPutReturnsNoEvent) {
  Putter() = [] {
    s_vpi_value val = {};
    val.format = vpiBinStrVal;
    val.value.str = VpiText("2");
    s_vpi_time time = {vpiSimTime, 0, 1, 0.0};
    results.returned.push_back(
        vpi_put_value(vpi_handle_by_name(VpiText("top.v"), nullptr), &val,
                      &time, vpiInertialDelay | vpiReturnEvent));
  };
  Run(kSampledAt3And5);
  EXPECT_EQ(results.returned, (std::vector<vpiHandle>{nullptr}));
}

TEST_F(TimedPutsOfARun, AForceOrAReleaseReturnsNoEvent) {
  Putter() = [] {
    results.returned.push_back(
        PutInt("top.v", 6, vpiForceFlag | vpiReturnEvent, 3));
    results.read_at_once.push_back(IntOf("top.v"));
    results.returned.push_back(
        PutInt("top.v", 0, vpiReleaseFlag | vpiReturnEvent, 3));
  };
  Run(kSampledAt3And5);
  EXPECT_EQ(results.returned, (std::vector<vpiHandle>{nullptr, nullptr}));
  EXPECT_EQ(results.read_at_once, (std::vector<int>{6}));
}

TEST_F(TimedPutsOfARun, APureTransportPutReturnsAScheduledEvent) {
  Putter() = [] {
    vpiHandle event =
        PutInt("top.v", 6, vpiPureTransportDelay | vpiReturnEvent, 3);
    results.returned.push_back(event);
    results.type = vpi_get(vpiType, event);
    results.scheduled = vpi_get(vpiScheduled, event);
  };
  Run(kSampledAt3And5);
  ASSERT_NE(results.returned.at(0), nullptr);
  EXPECT_EQ(results.type, vpiSchedEvent);
  EXPECT_EQ(results.scheduled, 1);
  EXPECT_EQ(IntOf("top.v_at5"), 6);
}

TEST_F(TimedPutsOfARun, CancellingAnEventThatTookPlaceIsNoErrorAndKeepsIt) {
  Putter() = [] {
    if (results.event == nullptr) {
      results.event = PutInt("top.v", 6, vpiTransportDelay | vpiReturnEvent, 1);
      return;
    }
    results.scheduled = vpi_get(vpiScheduled, results.event);
    vpi_put_value(results.event, nullptr, nullptr, vpiCancelEvent);
    results.error = vpi_chk_error(nullptr);
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; int v, v_at4;\n"
      "  initial begin #1 $put; #2 $put; #1 v_at4 = v; end\n"
      "endmodule\n");
  EXPECT_EQ(results.scheduled, 0);
  EXPECT_EQ(results.error, 0);
  EXPECT_EQ(IntOf("top.v_at4"), 6);
}

TEST_F(TimedPutsOfARun,
       EventsAnInertialPutRemovedStayRemovedWhenItIsCancelled) {
  Putter() = [] {
    PutInt("top.v", 6, vpiTransportDelay, 3);
    vpiHandle event = PutInt("top.v", 7, vpiInertialDelay | vpiReturnEvent, 1);
    vpi_put_value(event, nullptr, nullptr, vpiCancelEvent);
  };
  Run(kSampledAt3And5);
  EXPECT_EQ(IntOf("top.v_at3"), 0);
  EXPECT_EQ(IntOf("top.v_at5"), 0);
}

}  // namespace
}  // namespace delta
