#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "fixture_vpi_run.h"
#include "simulator/scheduler.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

using namespace delta;

// Shared test fixture for the vpi_get_delays()/vpi_put_delays() suites. It
// wires a scheduler into a fresh VpiContext, installs it as the global context,
// and offers a helper to build a delay-bearing object of a given category
// carrying a supplied list of delays in source order.
class VpiDelaysSimBase : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a delay-bearing object of the given type carrying the supplied
  // delays, in source order. The handle is a VpiObject*, so the test sets the
  // category and stores the delays on it directly.
  VpiHandle MakeDelayObject(int type, std::vector<VpiDelayInfo> delays) {
    VpiHandle obj = vpi_ctx_.CreateModule("u", "u");
    obj->type = type;
    obj->delays = std::move(delays);
    return obj;
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

// The two delays vpi_get_delays read off the design's continuous assignment
// before vpi_put_delays gave it 5 and 6.
inline std::vector<uint32_t>& ContAssignDelaysRead() {
  static std::vector<uint32_t> read;
  return read;
}

inline PLI_INT32 ReadAndPutContAssignDelays(PLI_BYTE8* /*user_data*/) {
  vpiHandle it =
      vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
  vpiHandle ca = it != nullptr ? vpi_scan(it) : nullptr;
  if (it != nullptr) vpi_release_handle(it);
  s_vpi_time times[2] = {};
  s_vpi_delay delay = {};
  delay.da = times;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_get_delays(ca, &delay);
  ContAssignDelaysRead() = {times[0].low, times[1].low};
  times[0].low = 5;
  times[1].low = 6;
  vpi_put_delays(ca, &delay);
  return 0;
}

// A run whose `$delays` at time 1 reads the delays of `assign #(3, 4) y = a`
// and puts 5 and 6, `a` then rising at 10 and falling at 20, `rose` and `fell`
// recording when `y` followed.
class ContAssignDelaysOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$delays");
    data.calltf = &ReadAndPutContAssignDelays;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
    Run("`timescale 1ns/1ns\n"
        "module top; logic a = 0; wire y; int rose, fell;\n"
        "  assign #(3, 4) y = a;\n"
        "  always @(y) if (y === 1'b1) rose = $time; else fell = $time;\n"
        "  initial begin #1 $delays; #9 a = 1; #10 a = 0; #10; end\n"
        "endmodule\n");
  }
};
