#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiHandleByIndexSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiHandleByIndexSim, HandleByIndexReturnCorrectChild) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);
  auto* port_b = vpi_ctx_.CreatePort("b", kVpiOutput, mod);

  vpiHandle result = vpi_handle_by_index(mod, 1);
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result, port_b);
}

TEST_F(VpiHandleByIndexSim, HandleByIndexNullParentReturnsNullptr) {
  vpiHandle result = vpi_handle_by_index(nullptr, 0);
  EXPECT_EQ(result, nullptr);
}

// §38.19: an index that names no sub-object does not lead to a legal index
// select expression, so the routine returns a null handle.
TEST_F(VpiHandleByIndexSim, HandleByIndexOutOfRangeReturnsNullptr) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpiHandle result = vpi_handle_by_index(mod, 99);
  EXPECT_EQ(result, nullptr);
}

// §38.19: unless otherwise specified, calling vpi_handle_by_index() for a
// protected reference object is an error - no handle is produced and the error
// status is recorded for vpi_chk_error() (§38.2).
TEST_F(VpiHandleByIndexSim, HandleByIndexProtectedObjectIsAnError) {
  auto* mod = vpi_ctx_.CreateModule("top", "top");
  vpi_ctx_.CreatePort("a", kVpiInput, mod);
  mod->is_protected = true;

  vpiHandle result = vpi_handle_by_index(mod, 0);
  EXPECT_EQ(result, nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

// §38.19: the reference object must have the access-by-index property. A
// parameter offers no index-selected relationship, so even when it has a child
// at the requested index the routine builds no index select and returns null.
TEST_F(VpiHandleByIndexSim,
       HandleByIndexReferenceWithoutAccessByIndexReturnsNullptr) {
  auto* param = vpi_ctx_.CreateParameter("p", 0);
  vpi_ctx_.CreatePort("a", kVpiInput, param);  // gives param a child at index 0

  vpiHandle result = vpi_handle_by_index(param, 0);
  EXPECT_EQ(result, nullptr);
}

}  // namespace
}  // namespace delta
