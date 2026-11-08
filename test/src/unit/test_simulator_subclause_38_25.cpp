#include <gtest/gtest.h>

#include <filesystem>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_run_files.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiMcdFlushSim : public ::testing::Test {
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

TEST_F(VpiMcdFlushSim, FlushesSeveralChannelsSimultaneously) {
  char a[] = "a.txt";
  char b[] = "b.txt";
  PLI_UINT32 mcd_a = vpi_mcd_open(a);
  PLI_UINT32 mcd_b = vpi_mcd_open(b);
  ASSERT_NE(mcd_a, 0u);
  ASSERT_NE(mcd_b, 0u);

  vpi_ctx_.WriteMcdChannel(mcd_a, "first");
  vpi_ctx_.WriteMcdChannel(mcd_b, "second");

  EXPECT_EQ(vpi_mcd_flush(mcd_a | mcd_b), 0);
  EXPECT_EQ(vpi_ctx_.McdChannelFlushed(mcd_a), "first");
  EXPECT_EQ(vpi_ctx_.McdChannelFlushed(mcd_b), "second");
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd_a), "");
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd_b), "");
}

TEST_F(VpiMcdFlushSim, ReturnsNonzeroOnFailureAndLeavesBufferIntact) {
  char name[] = "fail.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  vpi_ctx_.WriteMcdChannel(mcd, "pending");
  vpi_ctx_.SetMcdFlushShouldFail(true);

  EXPECT_NE(vpi_mcd_flush(mcd), 0);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "pending");
  EXPECT_EQ(vpi_ctx_.McdChannelFlushed(mcd), "");
}

TEST_F(VpiMcdFlushSim, OnlyChannelsNamedByDescriptorAreFlushed) {
  char a[] = "named.txt";
  char b[] = "other.txt";
  PLI_UINT32 mcd_a = vpi_mcd_open(a);
  PLI_UINT32 mcd_b = vpi_mcd_open(b);
  ASSERT_NE(mcd_a, 0u);
  ASSERT_NE(mcd_b, 0u);

  vpi_ctx_.WriteMcdChannel(mcd_a, "flush-me");
  vpi_ctx_.WriteMcdChannel(mcd_b, "keep-me");

  EXPECT_EQ(vpi_mcd_flush(mcd_a), 0);
  EXPECT_EQ(vpi_ctx_.McdChannelFlushed(mcd_a), "flush-me");
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd_a), "");
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd_b), "keep-me");
  EXPECT_EQ(vpi_ctx_.McdChannelFlushed(mcd_b), "");
}

TEST_F(VpiMcdFlushSim, FlushingDescriptorWithNoPendingOutputSucceeds) {
  char name[] = "quiet.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  EXPECT_EQ(vpi_mcd_flush(mcd), 0);
  EXPECT_EQ(vpi_ctx_.McdChannelFlushed(mcd), "");
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
}

TEST_F(VpiMcdFlushSim, WhatAPrintLeftOnAChannelIsWhatTheFlushCommits) {
  char name[] = "printed.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  char format[] = "%s=%d\n";
  char label[] = "count";
  ASSERT_EQ(vpi_mcd_printf(mcd, format, label, 3), 8);
  ASSERT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "count=3\n");

  EXPECT_EQ(vpi_mcd_flush(mcd), 0);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
  EXPECT_EQ(vpi_ctx_.McdChannelFlushed(mcd), "count=3\n");
}

TEST_F(VpiMcdFlushSim, FlushingChannelOneCommitsTheToolsOutputChannelAndLog) {
  char format[] = "through-channel-one\n";
  ASSERT_EQ(vpi_mcd_printf(1, format), 20);
  ASSERT_EQ(vpi_ctx_.OutputChannelBuffer(), "through-channel-one\n");
  ASSERT_EQ(vpi_ctx_.LogFileBuffer(), "through-channel-one\n");

  EXPECT_EQ(vpi_mcd_flush(1), 0);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
  EXPECT_EQ(vpi_ctx_.OutputChannelFlushed(), "through-channel-one\n");
  EXPECT_EQ(vpi_ctx_.LogFileFlushed(), "through-channel-one\n");
}

TEST_F(VpiMcdFlushSim, AToolFlushFailureIsReportedForChannelOne) {
  char format[] = "pending\n";
  ASSERT_EQ(vpi_mcd_printf(1, format), 8);
  vpi_ctx_.SetFlushShouldFail(true);

  EXPECT_NE(vpi_mcd_flush(1), 0);
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), "pending\n");
}

PLI_INT32 run_flush_result = 1;

class FlushOfAFopenedFile : public RunFilesRun {
 protected:
  static PLI_INT32 FlushIt(PLI_BYTE8*) {
    run_flush_result = vpi_mcd_flush(DescriptorIn("top.mcd"));
    return 0;
  }
};

TEST_F(FlushOfAFopenedFile, ItsTextIsInTheFile) {
  RegisterTask("$flush_it", &FlushIt);
  Run("module top; integer mcd;\n"
      "  initial begin\n"
      "    mcd = $fopen(\"mcd.txt\");\n"
      "    $fwrite(mcd, \"before\");\n"
      "    $flush_it;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(run_flush_result, 0);
  EXPECT_EQ(FileText("mcd.txt"), "before");
}

PLI_INT32 unopened_flush_result = 1;
PLI_INT32 refused_flush_result = 0;

class FlushOfARunChannel : public RunFilesRun {
 protected:
  static PLI_INT32 FlushUnopened(PLI_BYTE8*) {
    unopened_flush_result = vpi_mcd_flush(PLI_UINT32{1} << 20);
    return 0;
  }
  static PLI_INT32 FlushRefused(PLI_BYTE8*) {
    const PLI_UINT32 kMcd = vpi_mcd_open(VpiText("/dev/full"));
    vpi_mcd_printf(kMcd, VpiText("lost"));
    refused_flush_result = vpi_mcd_flush(kMcd);
    vpi_mcd_close(kMcd);
    return 0;
  }
};

TEST_F(FlushOfARunChannel, AChannelWithNoFileFlushesWithoutError) {
  RegisterTask("$flush_unopened", &FlushUnopened);
  Run("module top; initial $flush_unopened; endmodule\n");
  EXPECT_EQ(unopened_flush_result, 0);
}

TEST_F(FlushOfARunChannel, AFlushTheFileRefusesIsReported) {
  if (!std::filesystem::exists("/dev/full")) GTEST_SKIP() << "no /dev/full";
  RegisterTask("$flush_refused", &FlushRefused);
  Run("module top; initial $flush_refused; endmodule\n");
  EXPECT_NE(refused_flush_result, 0);
}

}  // namespace
}  // namespace delta
