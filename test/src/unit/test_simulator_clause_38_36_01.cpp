#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.36.1 covers the simulation-event callback reasons registered through
// vpi_register_cb(). The single registration-time rule this subclause's text
// states - distinct from the firing semantics of the individual reasons - is
// that a cbForce, cbRelease, or cbDisable callback may not be placed on a
// variable bit-select. These tests observe vpi_register_cb() applying that
// rule.
class VpiSimEventCb : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a handle to a single bit-select of a declared variable.
  vpiHandle MakeBitSelectHandle(const char* name) {
    sim_ctx_.CreateVariable(name, 1);
    vpi_ctx_.Attach(sim_ctx_);
    vpiHandle h = vpi_handle_by_name(name, nullptr);
    if (h) h->type = vpiBitSelect;
    return h;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.36.1: placing a cbForce callback on a variable bit-select is illegal;
// vpi_register_cb() rejects it and reports an error.
TEST_F(VpiSimEventCb, ForceCallbackOnBitSelectRejected) {
  vpiHandle bit = MakeBitSelectHandle("f");
  ASSERT_NE(bit, nullptr);

  s_cb_data cb = {};
  cb.reason = cbForce;
  cb.obj = bit;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.36.1: the same prohibition holds for a cbRelease callback.
TEST_F(VpiSimEventCb, ReleaseCallbackOnBitSelectRejected) {
  vpiHandle bit = MakeBitSelectHandle("r");
  ASSERT_NE(bit, nullptr);

  s_cb_data cb = {};
  cb.reason = cbRelease;
  cb.obj = bit;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.36.1: and for a cbDisable callback.
TEST_F(VpiSimEventCb, DisableCallbackOnBitSelectRejected) {
  vpiHandle bit = MakeBitSelectHandle("d");
  ASSERT_NE(bit, nullptr);

  s_cb_data cb = {};
  cb.reason = cbDisable;
  cb.obj = bit;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.36.1: the prohibition is specific to a bit-select target. A cbForce
// callback on the whole variable (not a bit-select) is a legal registration and
// produces a callback handle.
TEST_F(VpiSimEventCb, ForceCallbackOnWholeVariableAccepted) {
  sim_ctx_.CreateVariable("whole", 1);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle var = vpi_handle_by_name("whole", nullptr);
  ASSERT_NE(var, nullptr);

  s_cb_data cb = {};
  cb.reason = cbForce;
  cb.obj = var;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.1: for a force/release callback a NULL obj means every force or
// release should generate a callback - it is not a bit-select, so registration
// is accepted rather than rejected by the bit-select rule.
TEST_F(VpiSimEventCb, ForceCallbackWithNullObjectAccepted) {
  s_cb_data cb = {};
  cb.reason = cbForce;
  cb.obj = nullptr;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §38.36.1: the prohibition names only cbForce, cbRelease, and cbDisable. A
// callback for a different reason (here cbValueChange) on the same variable
// bit-select is outside the rule and is registered normally.
TEST_F(VpiSimEventCb, ValueChangeCallbackOnBitSelectAccepted) {
  vpiHandle bit = MakeBitSelectHandle("v");
  ASSERT_NE(bit, nullptr);

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = bit;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

}  // namespace
}  // namespace delta
