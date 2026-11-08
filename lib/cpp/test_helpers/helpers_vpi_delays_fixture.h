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

class VpiDelaysSimBase : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

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

inline std::vector<uint32_t>& ContAssignDelaysRead() {
  static std::vector<uint32_t> read;
  return read;
}

inline PLI_INT32 ReadAndPutContAssignDelays(PLI_BYTE8*) {
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

class ContAssignDelaysOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$delays");
    data.calltf = &ReadAndPutContAssignDelays;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
    Run("module top; timeunit 1ns; timeprecision 1ns; logic a = 0; wire y; int "
        "rose, fell;\n"
        "  assign #(3, 4) y = a;\n"
        "  always @(y) if (y === 1'b1) rose = $time; else fell = $time;\n"
        "  initial begin #1 $delays; #9 a = 1; #10 a = 0; #10; end\n"
        "endmodule\n");
  }
};
