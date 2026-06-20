#pragma once

#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "common/arena.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

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
