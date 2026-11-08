#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiFlushSim : public ::testing::Test {
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

TEST_F(VpiFlushSim, FlushCommitsOutputChannelAndLogFile) {
  vpi_ctx_.WriteOutputChannel("channel-pending");
  vpi_ctx_.WriteLogFile("log-pending");
  ASSERT_FALSE(vpi_ctx_.OutputChannelBuffer().empty());
  ASSERT_FALSE(vpi_ctx_.LogFileBuffer().empty());

  EXPECT_EQ(vpi_flush(), 0);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
  EXPECT_EQ(vpi_ctx_.OutputChannelFlushed(), "channel-pending");
  EXPECT_EQ(vpi_ctx_.LogFileFlushed(), "log-pending");
}

TEST_F(VpiFlushSim, ReturnsNonzeroOnFailureLeavingBuffersIntact) {
  vpi_ctx_.WriteOutputChannel("channel-pending");
  vpi_ctx_.WriteLogFile("log-pending");
  vpi_ctx_.SetFlushShouldFail(true);

  EXPECT_NE(vpi_flush(), 0);

  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), "channel-pending");
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), "log-pending");
  EXPECT_TRUE(vpi_ctx_.OutputChannelFlushed().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileFlushed().empty());
}

TEST_F(VpiFlushSim, FlushWithNothingBufferedSucceeds) {
  EXPECT_EQ(vpi_flush(), 0);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.OutputChannelFlushed().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileFlushed().empty());
}

TEST_F(VpiFlushSim, BuffersPreservedByFailedFlushAreCommittedOnRetry) {
  vpi_ctx_.WriteOutputChannel("channel-pending");
  vpi_ctx_.WriteLogFile("log-pending");

  vpi_ctx_.SetFlushShouldFail(true);
  ASSERT_NE(vpi_flush(), 0);

  vpi_ctx_.SetFlushShouldFail(false);
  EXPECT_EQ(vpi_flush(), 0);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
  EXPECT_EQ(vpi_ctx_.OutputChannelFlushed(), "channel-pending");
  EXPECT_EQ(vpi_ctx_.LogFileFlushed(), "log-pending");
}

TEST_F(VpiFlushSim, WhatAPrintLeftPendingIsWhatTheFlushCommits) {
  char format[] = "%s=%d\n";
  char name[] = "count";
  ASSERT_EQ(vpi_printf(format, name, 3), 8);
  ASSERT_EQ(vpi_ctx_.OutputChannelBuffer(), "count=3\n");
  ASSERT_EQ(vpi_ctx_.LogFileBuffer(), "count=3\n");

  EXPECT_EQ(vpi_flush(), 0);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
  EXPECT_EQ(vpi_ctx_.OutputChannelFlushed(), "count=3\n");
  EXPECT_EQ(vpi_ctx_.LogFileFlushed(), "count=3\n");
}

TEST_F(VpiFlushSim, AFlushResetsThePendingErrorStatus) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("missing_dollar");
  ASSERT_EQ(vpi_register_systf(&data), nullptr);
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);

  EXPECT_EQ(vpi_flush(), 0);

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

}  // namespace
}  // namespace delta
