#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiVlogInfoSim : public ::testing::Test {
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

// §38.17: vpi_get_vlog_info() supplies the product and version strings, and
// reports 1 (true) on success. With no invocation options recorded there are
// zero argv entries.
TEST_F(VpiVlogInfoSim, GetVlogInfoReturnsProductAndVersion) {
  SVpiVlogInfo info = {};
  EXPECT_EQ(vpi_get_vlog_info(&info), 1);
  ASSERT_NE(info.product, nullptr);
  ASSERT_NE(info.version, nullptr);
  EXPECT_STREQ(info.product, "DeltaHDL");
  EXPECT_STREQ(info.version, "0.1.0");
  EXPECT_EQ(info.argc, 0);
}

// §38.17: the routine shall return 0 (false) on failure. A null result
// structure has nowhere to place the information, so the call fails.
TEST_F(VpiVlogInfoSim, GetVlogInfoReturnsZeroOnFailure) {
  EXPECT_EQ(vpi_get_vlog_info(nullptr), 0);
}

// §38.17: argc is the number of invocation options and argv carries their
// values; there shall be argc entries in argv, each a NUL-terminated string,
// and entry zero shall be the tool's name.
TEST_F(VpiVlogInfoSim, GetVlogInfoReportsInvocationCommandLine) {
  vpi_ctx_.SetInvocationArguments("delta-sim", {"-top", "dut", "+define+FOO"});

  SVpiVlogInfo info = {};
  EXPECT_EQ(vpi_get_vlog_info(&info), 1);

  // There shall be argc entries in argv (tool name plus three options).
  ASSERT_EQ(info.argc, 4);
  ASSERT_NE(info.argv, nullptr);

  // Entry zero shall be the tool's name; the remaining entries are the options
  // in command-line order, each a distinct NUL-terminated string.
  EXPECT_STREQ(info.argv[0], "delta-sim");
  EXPECT_STREQ(info.argv[1], "-top");
  EXPECT_STREQ(info.argv[2], "dut");
  EXPECT_STREQ(info.argv[3], "+define+FOO");
}

// §38.17: the minimal non-empty command line is the tool name alone with no
// invocation options. There shall then be exactly one argv entry, and entry
// zero shall hold the tool's name, with argv still a valid pointer array.
TEST_F(VpiVlogInfoSim, GetVlogInfoReportsToolNameWhenNoOptions) {
  vpi_ctx_.SetInvocationArguments("delta-sim", {});

  SVpiVlogInfo info = {};
  EXPECT_EQ(vpi_get_vlog_info(&info), 1);

  ASSERT_EQ(info.argc, 1);
  ASSERT_NE(info.argv, nullptr);
  EXPECT_STREQ(info.argv[0], "delta-sim");
}

}
}
