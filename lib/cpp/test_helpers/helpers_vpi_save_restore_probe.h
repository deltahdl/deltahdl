#pragma once

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

using namespace delta;

struct SingleRead {
  int id = 0;
  int request = 0;
  int returned = -1;
  char buf[64] = {};
};

inline int ReadOnceCb(s_cb_data* cb) {
  auto* p = reinterpret_cast<SingleRead*>(cb->user_data);
  p->returned = vpi_get_data(p->id, p->buf, p->request);
  return 0;
}

struct DoubleRead {
  int id = 0;
  int req1 = 0;
  int req2 = 0;
  int ret1 = -1;
  int ret2 = -1;
  char buf1[64] = {};
  char buf2[64] = {};
};

inline int ReadTwiceCb(s_cb_data* cb) {
  auto* p = reinterpret_cast<DoubleRead*>(cb->user_data);
  p->ret1 = vpi_get_data(p->id, p->buf1, p->req1);
  p->ret2 = vpi_get_data(p->id, p->buf2, p->req2);
  return 0;
}

class VpiSaveRestoreSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void DispatchWith(int reason, int (*cb_rtn)(s_cb_data*), void* probe) {
    s_cb_data reg = {};
    reg.reason = reason;
    reg.cb_rtn = cb_rtn;
    reg.user_data = static_cast<PLI_BYTE8*>(probe);
    ASSERT_NE(vpi_register_cb(&reg), nullptr);
    vpi_ctx_.DispatchCallbacks(reason);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  Diagnosed diagnosed_{diag_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};
