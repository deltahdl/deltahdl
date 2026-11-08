#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_run_files.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiMcdCloseSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;

  static constexpr PLI_UINT32 kLsbChannel = 0x00000001u;
};

TEST_F(VpiMcdCloseSim, ClosesFileAndReturnsZeroOnSuccess) {
  char name[] = "trace.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);
  ASSERT_TRUE(vpi_ctx_.IsMcdFileOpen("trace.log"));

  EXPECT_EQ(vpi_mcd_close(mcd), 0u);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("trace.log"));

  char again[] = "again.log";
  EXPECT_EQ(vpi_mcd_open(again), mcd);
}

TEST_F(VpiMcdCloseSim, ClosesSeveralChannelsSimultaneously) {
  char a[] = "a.txt";
  char b[] = "b.txt";
  PLI_UINT32 mcd_a = vpi_mcd_open(a);
  PLI_UINT32 mcd_b = vpi_mcd_open(b);
  ASSERT_NE(mcd_a, 0u);
  ASSERT_NE(mcd_b, 0u);

  EXPECT_EQ(vpi_mcd_close(mcd_a | mcd_b), 0u);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("a.txt"));
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("b.txt"));
}

TEST_F(VpiMcdCloseSim, ReturnsUnclosedChannelsOnError) {
  char name[] = "open.log";
  PLI_UINT32 open_mcd = vpi_mcd_open(name);
  ASSERT_NE(open_mcd, 0u);

  PLI_UINT32 stale = (open_mcd == 0x40000000u) ? 0x20000000u : 0x40000000u;
  ASSERT_EQ(open_mcd & stale, 0u);

  EXPECT_EQ(vpi_mcd_close(open_mcd | stale), stale);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("open.log"));
}

TEST_F(VpiMcdCloseSim, PredefinedDescriptorOneCannotBeClosed) {
  EXPECT_EQ(vpi_mcd_close(kLsbChannel), kLsbChannel);

  char name[] = "real.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);
  EXPECT_EQ(vpi_mcd_close(mcd | kLsbChannel), kLsbChannel);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("real.log"));
}

TEST_F(VpiMcdCloseSim, ReportsAllUnclosedChannelsWhileClosingTheRest) {
  char name[] = "live.log";
  PLI_UINT32 live = vpi_mcd_open(name);
  ASSERT_NE(live, 0u);

  PLI_UINT32 stale = (live == 0x40000000u) ? 0x20000000u : 0x40000000u;
  ASSERT_EQ(live & stale, 0u);

  PLI_UINT32 result = vpi_mcd_close(live | stale | kLsbChannel);
  EXPECT_EQ(result, stale | kLsbChannel);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("live.log"));
}

TEST_F(VpiMcdCloseSim, ClosesDescriptorOpenedByFopen) {
  PLI_UINT32 fopen_mcd = 0x00000004u;
  vpi_ctx_.RegisterFopenMcdFile("from_fopen.log", fopen_mcd);
  ASSERT_TRUE(vpi_ctx_.IsMcdFileOpen("from_fopen.log"));

  EXPECT_EQ(vpi_mcd_close(fopen_mcd), 0u);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("from_fopen.log"));

  char filler[] = "filler.log";
  EXPECT_EQ(vpi_mcd_open(filler), 0x00000002u);
  char fresh[] = "fresh.log";
  EXPECT_EQ(vpi_mcd_open(fresh), fopen_mcd);
}

TEST_F(VpiMcdCloseSim, ClosesAnFdOpenedByFopen) {
  PLI_UINT32 fopen_fd = 0x80000005u;
  vpi_ctx_.RegisterFopenMcdFile("opened_as_fd.log", fopen_fd);

  char other[] = "channel_three.log";
  PLI_UINT32 other_mcd = vpi_mcd_open(other);
  ASSERT_NE(other_mcd, 0u);

  EXPECT_EQ(vpi_mcd_close(fopen_fd), 0u);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("opened_as_fd.log"));

  EXPECT_TRUE(vpi_ctx_.IsMcdFileOpen("channel_three.log"));
}

TEST_F(VpiMcdCloseSim, AnFdNamingNoOpenFileIsReportedBack) {
  PLI_UINT32 unknown_fd = 0x80000007u;

  EXPECT_EQ(vpi_mcd_close(unknown_fd), unknown_fd);
}

PLI_UINT32 fd_close_result = 1;
PLI_UINT32 mcd_close_result = 1;
PLI_UINT32 unopened_close_result = 0;

class CloseOfAFopenedFile : public RunFilesRun {
 protected:
  static PLI_INT32 CloseBoth(PLI_BYTE8*) {
    fd_close_result = vpi_mcd_close(DescriptorIn("top.fd"));
    mcd_close_result = vpi_mcd_close(DescriptorIn("top.mcd"));
    unopened_close_result = vpi_mcd_close(PLI_UINT32{1} << 20);
    return 0;
  }
};

TEST_F(CloseOfAFopenedFile, BothFormsAreClosed) {
  RegisterTask("$close_both", &CloseBoth);
  Run("module top; integer fd, mcd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"fd.txt\", \"w\");\n"
      "    mcd = $fopen(\"mcd.txt\");\n"
      "    $close_both;\n"
      "    $fdisplay(fd, \"after\");\n"
      "    $fdisplay(mcd, \"after\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(fd_close_result, 0u);
  EXPECT_EQ(mcd_close_result, 0u);
  EXPECT_EQ(unopened_close_result, PLI_UINT32{1} << 20);
  EXPECT_EQ(FileText("fd.txt"), "");
  EXPECT_EQ(FileText("mcd.txt"), "");
}

constexpr PLI_UINT32 kUnopenedFd = SimContext::kFdMsb | 7u;

std::vector<PLI_UINT32> stream_close_results;
PLI_UINT32 unopened_fd_close_result = 0;

class CloseOfAStreamFd : public RunFilesRun {
 protected:
  static PLI_INT32 CloseStreams(PLI_BYTE8*) {
    for (const PLI_UINT32 kFd :
         {SimContext::kStdinFd, SimContext::kStdoutFd, SimContext::kStderrFd}) {
      stream_close_results.push_back(vpi_mcd_close(kFd));
    }
    unopened_fd_close_result = vpi_mcd_close(kUnopenedFd);
    return 0;
  }
};

TEST_F(CloseOfAStreamFd, NeitherAStreamNorAnUnopenedFdIsClosed) {
  RegisterTask("$close_streams", &CloseStreams);
  Run("module top; initial $close_streams; endmodule\n");
  EXPECT_EQ(
      stream_close_results,
      (std::vector<PLI_UINT32>{SimContext::kStdinFd, SimContext::kStdoutFd,
                               SimContext::kStderrFd}));
  EXPECT_EQ(unopened_fd_close_result, kUnopenedFd);
}

}  // namespace
}  // namespace delta
