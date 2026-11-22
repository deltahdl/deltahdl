#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiHandleByMultiIndexSim : public ::testing::Test {
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

TEST_F(VpiHandleByMultiIndexSim, NullParentReturnsNullptr) {
  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(nullptr, 1, indices), nullptr);
}

TEST_F(VpiHandleByMultiIndexSim, ProtectedReferenceObjectIsAnError) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  bus->is_protected = true;

  int indices[] = {0};
  EXPECT_EQ(vpi_handle_by_multi_index(VpiHandleOf(bus), 1, indices), nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

TEST_F(VpiHandleByMultiIndexSim, ANullIndexArrayNamesNothing) {
  auto* bus = vpi_ctx_.CreateNetObj("bus", nullptr, 8);
  EXPECT_EQ(vpi_handle_by_multi_index(VpiHandleOf(bus), 1, nullptr), nullptr);
}
}  // namespace
}  // namespace delta
