#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiFreeObjectDeprecated : public ::testing::Test {
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

TEST_F(VpiFreeObjectDeprecated, RecordsADeprecationDiagnostic) {
  VpiObject obj;
  obj.type = vpiModule;

  vpi_free_object(VpiHandleOf(&obj));

  const s_vpi_error_info& err = vpi_ctx_.LastError();
  EXPECT_EQ(err.level, kVpiWarning);
  ASSERT_NE(err.message, nullptr);
  EXPECT_NE(std::string(err.message).find("vpi_release_handle"),
            std::string::npos);
  EXPECT_NE(std::string(err.message).find("deprecated"), std::string::npos);
}

TEST_F(VpiFreeObjectDeprecated, ReplacementRoutineCarriesTheLiveRelease) {
  VpiObject obj;
  obj.type = vpiModule;

  ASSERT_EQ(vpi_free_object(VpiHandleOf(&obj)), 0);
  ASSERT_FALSE(vpi_ctx_.HandleReleased(&obj));

  EXPECT_EQ(vpi_release_handle(VpiHandleOf(&obj)), 1);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(&obj));
}

TEST_F(VpiFreeObjectDeprecated, DeprecationAppliesEvenToANullHandle) {
  EXPECT_EQ(vpi_free_object(nullptr), 0);

  const s_vpi_error_info& err = vpi_ctx_.LastError();
  EXPECT_EQ(err.level, kVpiWarning);
  ASSERT_NE(err.message, nullptr);
  EXPECT_NE(std::string(err.message).find("vpi_release_handle"),
            std::string::npos);
}

}  // namespace
}  // namespace delta
