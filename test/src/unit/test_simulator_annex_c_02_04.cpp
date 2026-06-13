#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// Annex C.2.4: vpi_free_object().
//
// The semantics of this VPI routine were clarified to account for handle
// validity and the dynamic data of the SystemVerilog object model, and in doing
// so it was renamed vpi_release_handle(). IEEE 1800-2023 therefore deprecates
// vpi_free_object(): the old name no longer denotes a supported operation. The
// simulator carries this deprecation - a call to the deprecated routine performs
// no release, reports failure, and records a deprecation diagnostic that names
// the replacement - while the renamed routine keeps the live functionality.
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

// The deprecation is observable: the call records a VPI diagnostic that names
// vpi_release_handle() as the replacement, so a program reaching the deprecated
// name is told where the live routine moved.
TEST_F(VpiFreeObjectDeprecated, RecordsADeprecationDiagnostic) {
  VpiObject obj;
  obj.type = vpiModule;

  vpi_free_object(&obj);

  const VpiErrorInfo& err = vpi_ctx_.LastError();
  EXPECT_EQ(err.state, kVpiWarning);
  ASSERT_NE(err.message, nullptr);
  EXPECT_NE(std::string(err.message).find("vpi_release_handle"),
            std::string::npos);
  EXPECT_NE(std::string(err.message).find("deprecated"), std::string::npos);
}

// The rename carries the functionality the deprecated name lost. Where
// vpi_free_object() refused to act, vpi_release_handle() releases the same valid
// handle and reports success - demonstrating which routine is now the live one.
TEST_F(VpiFreeObjectDeprecated, ReplacementRoutineCarriesTheLiveRelease) {
  VpiObject obj;
  obj.type = vpiModule;

  ASSERT_EQ(vpi_free_object(&obj), 0);
  ASSERT_FALSE(vpi_ctx_.HandleReleased(&obj));

  EXPECT_EQ(vpi_release_handle(&obj), 1);
  EXPECT_TRUE(vpi_ctx_.HandleReleased(&obj));
}

// Edge case: the deprecation is unconditional. The deprecated routine carries no
// working path for any handle, so even a null handle - one a live routine would
// dismiss as naming nothing - still draws the deprecation diagnostic and the
// failure return. There is no argument for which vpi_free_object() does real
// work; it only ever reports that it is gone.
TEST_F(VpiFreeObjectDeprecated, DeprecationAppliesEvenToANullHandle) {
  EXPECT_EQ(vpi_free_object(nullptr), 0);

  const VpiErrorInfo& err = vpi_ctx_.LastError();
  EXPECT_EQ(err.state, kVpiWarning);
  ASSERT_NE(err.message, nullptr);
  EXPECT_NE(std::string(err.message).find("vpi_release_handle"),
            std::string::npos);
}

}  // namespace
}  // namespace delta
