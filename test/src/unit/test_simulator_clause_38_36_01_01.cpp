#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.36.1.1 governs cbStmt callbacks placed on individual statements. It states
// one registration-time prohibition (a cbStmt callback may not be placed on a
// statement in a protected portion of the code), one repetition rule (multiple
// identical registrations produce multiple callbacks), and the fixed contents of
// the s_cb_data structure delivered to the routine (value always NULL, index
// always 0, and a NULL time pointer when registered with vpiSuppressTime). These
// tests observe vpi_register_cb()/DispatchCallbacks() applying those rules.

// Recorder for the contents of the s_cb_data structure the simulator hands to a
// cbStmt routine, so a test can observe the dispatch-time field guarantees.
int g_stmt_calls = 0;
VpiValue* g_stmt_value = reinterpret_cast<VpiValue*>(1);
int g_stmt_index = -1;
VpiTime* g_stmt_time = reinterpret_cast<VpiTime*>(1);

int RecordStmtCb(VpiCbData* data) {
  ++g_stmt_calls;
  if (data) {
    g_stmt_value = data->value;
    g_stmt_index = data->index;
    g_stmt_time = data->time;
  }
  return 0;
}

class VpiStmtCallback : public ::testing::Test {
 protected:
  void SetUp() override {
    g_stmt_calls = 0;
    g_stmt_value = reinterpret_cast<VpiValue*>(1);
    g_stmt_index = -1;
    g_stmt_time = reinterpret_cast<VpiTime*>(1);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a handle that stands for a statement (here a named-begin block, one of
  // the cbStmt-eligible objects). `protect` marks it as residing in a protected
  // portion of the code.
  vpiHandle MakeStatementHandle(const char* name, bool protect) {
    sim_ctx_.CreateVariable(name, 1);
    vpi_ctx_.Attach(sim_ctx_);
    vpiHandle h = vpi_handle_by_name(name, nullptr);
    if (h) {
      h->type = vpiNamedBegin;
      h->is_protected = protect;
    }
    return h;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.36.1.1: placing a cbStmt callback on a statement that resides in a
// protected portion of the code is not allowed; vpi_register_cb() returns NULL
// and records an error.
TEST_F(VpiStmtCallback, ProtectedStatementRejected) {
  vpiHandle stmt = MakeStatementHandle("p", /*protect=*/true);
  ASSERT_NE(stmt, nullptr);

  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.obj = stmt;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
}

// §38.36.1.1: the prohibition is specific to protected code. A cbStmt callback
// on an ordinary, unprotected statement is a legal registration and yields a
// callback handle.
TEST_F(VpiStmtCallback, UnprotectedStatementAccepted) {
  vpiHandle stmt = MakeStatementHandle("u", /*protect=*/false);
  ASSERT_NE(stmt, nullptr);

  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.obj = stmt;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.1.1: the protected-code prohibition is specific to the cbStmt reason.
// A callback for another reason (here cbValueChange) placed on the same
// protected handle is outside this rule, so the cbStmt guard does not reject it.
TEST_F(VpiStmtCallback, ProtectedHandleRejectionIsSpecificToStmtReason) {
  vpiHandle stmt = MakeStatementHandle("s", /*protect=*/true);
  ASSERT_NE(stmt, nullptr);

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = stmt;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.1.1: multiple calls to vpi_register_cb() with the same data shall
// result in multiple callbacks. Registering the identical cbStmt data twice and
// dispatching the reason once invokes the routine twice.
TEST_F(VpiStmtCallback, MultipleIdenticalRegistrationsProduceMultipleCallbacks) {
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = &RecordStmtCb;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);

  EXPECT_EQ(g_stmt_calls, 2);
}

// §38.36.1.1: in the s_cb_data delivered to a cbStmt routine the value field is
// always NULL and the index field is always 0, regardless of what was supplied
// at registration.
TEST_F(VpiStmtCallback, DispatchedDataHasNullValueAndZeroIndex) {
  VpiValue supplied_value = {};
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = &RecordStmtCb;
  cb.value = &supplied_value;
  cb.index = 5;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);

  ASSERT_EQ(g_stmt_calls, 1);
  EXPECT_EQ(g_stmt_value, nullptr);
  EXPECT_EQ(g_stmt_index, 0);
}

// §38.36.1.1: when a cbStmt callback was registered with a vpiSuppressTime time
// type, no time is passed to the routine - the time pointer in the delivered
// s_cb_data is set to NULL.
TEST_F(VpiStmtCallback, SuppressTimeNullsDispatchedTimePointer) {
  VpiTime t = {};
  t.type = vpiSuppressTime;
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = &RecordStmtCb;
  cb.time = &t;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);

  ASSERT_EQ(g_stmt_calls, 1);
  EXPECT_EQ(g_stmt_time, nullptr);
}

// §38.36.1.1: the NULL-time rule is specific to vpiSuppressTime. When a real
// time type (here vpiSimTime) is requested, the routine receives a time pointer
// rather than NULL.
TEST_F(VpiStmtCallback, NonSuppressTimePreservesDispatchedTimePointer) {
  VpiTime t = {};
  t.type = vpiSimTime;
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = &RecordStmtCb;
  cb.time = &t;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchCallbacks(cbStmt);

  ASSERT_EQ(g_stmt_calls, 1);
  EXPECT_EQ(g_stmt_time, &t);
}

}  // namespace
}  // namespace delta
