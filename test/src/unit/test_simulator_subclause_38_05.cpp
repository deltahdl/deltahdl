#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

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

// §38.5: vpi_flush() shall flush the output buffers for the simulator's output
// channel and the current log file. Buffered text on both channels is committed
// and the buffers are emptied, and the routine reports success with 0.
TEST_F(VpiFlushSim, FlushCommitsOutputChannelAndLogFile) {
  vpi_ctx_.WriteOutputChannel("channel-pending");
  vpi_ctx_.WriteLogFile("log-pending");
  ASSERT_FALSE(vpi_ctx_.OutputChannelBuffer().empty());
  ASSERT_FALSE(vpi_ctx_.LogFileBuffer().empty());

  EXPECT_EQ(vpi_flush(), 0);

  // Both buffers are now empty and their text has been committed downstream.
  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
  EXPECT_EQ(vpi_ctx_.OutputChannelFlushed(), "channel-pending");
  EXPECT_EQ(vpi_ctx_.LogFileFlushed(), "log-pending");
}

// §38.5: when the flush cannot complete, vpi_flush() returns a nonzero value
// and leaves the buffered text untouched.
TEST_F(VpiFlushSim, ReturnsNonzeroOnFailureLeavingBuffersIntact) {
  vpi_ctx_.WriteOutputChannel("channel-pending");
  vpi_ctx_.WriteLogFile("log-pending");
  vpi_ctx_.SetFlushShouldFail(true);

  EXPECT_NE(vpi_flush(), 0);

  // Nothing was committed; the pending text is preserved for a later flush.
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), "channel-pending");
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), "log-pending");
  EXPECT_TRUE(vpi_ctx_.OutputChannelFlushed().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileFlushed().empty());
}

// §38.5 edge: flushing an idle simulator with no buffered text still succeeds
// and commits nothing.
TEST_F(VpiFlushSim, FlushWithNothingBufferedSucceeds) {
  EXPECT_EQ(vpi_flush(), 0);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.OutputChannelFlushed().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileFlushed().empty());
}

// §38.5 edge: text held back by a failed flush is preserved and committed by a
// subsequent successful flush, so no buffered output is lost across a failure.
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

// §38.5's Related routines name what fills the buffers it empties: vpi_printf()
// writes to the simulator's output channel and log file, so what a flush
// commits is the text a print left pending there. The tests above write the
// buffers directly, which leaves the routine flushing text nothing in the VPI
// surface put there; this one puts it there the way an application does.
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

// §38.2: "The error status shall be reset by any VPI routine call except
// vpi_chk_error()." vpi_flush() takes no arguments, so the one thing it has in
// common with every other routine of the clause is that call, and a flush after
// an error leaves no error pending behind it.
TEST_F(VpiFlushSim, AFlushResetsThePendingErrorStatus) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "missing_dollar";  // §36.9.1: a name with no dollar sign
  ASSERT_EQ(vpi_register_systf(&data), nullptr);
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);

  EXPECT_EQ(vpi_flush(), 0);

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

}  // namespace
}  // namespace delta
