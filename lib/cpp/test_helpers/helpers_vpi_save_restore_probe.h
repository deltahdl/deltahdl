#pragma once

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

using namespace delta;

// Shared probe routines and fixture for the vpi_get_data()/vpi_put_data()
// save/restart tests (§38.9 and §38.31). vpi_get_data() (and the write tests'
// read-back) are only legal from an application routine running for a
// save/restart reason. These probe routines stand in for such an application
// routine: the simulator invokes them from DispatchCallbacks (which sets the
// active callback reason), and they call the routine and record what it
// returned.

// A single vpi_get_data() call.
struct SingleRead {
  int id = 0;
  int request = 0;
  int returned = -1;
  char buf[64] = {};
};

inline int ReadOnceCb(VpiCbData* cb) {
  auto* p = static_cast<SingleRead*>(cb->user_data);
  p->returned = vpi_get_data(p->id, p->buf, p->request);
  return 0;
}

// Two successive vpi_get_data() calls for the same id.
struct DoubleRead {
  int id = 0;
  int req1 = 0;
  int req2 = 0;
  int ret1 = -1;
  int ret2 = -1;
  char buf1[64] = {};
  char buf2[64] = {};
};

inline int ReadTwiceCb(VpiCbData* cb) {
  auto* p = static_cast<DoubleRead*>(cb->user_data);
  p->ret1 = vpi_get_data(p->id, p->buf1, p->req1);
  p->ret2 = vpi_get_data(p->id, p->buf2, p->req2);
  return 0;
}

// Fixture that installs a VpiContext as the active global context and can
// register a callback for a reason and deliver it. The dispatch sets the active
// callback reason for the duration of the routine.
class VpiSaveRestoreSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Register `cb_rtn` for `reason`, carrying `probe`, then deliver it.
  void DispatchWith(int reason, int (*cb_rtn)(VpiCbData*), void* probe) {
    s_cb_data reg = {};
    reg.reason = reason;
    reg.cb_rtn = cb_rtn;
    reg.user_data = probe;
    ASSERT_NE(vpi_register_cb(&reg), nullptr);
    vpi_ctx_.DispatchCallbacks(reason);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};
