#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

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

// §38.25 (C1, C3): the descriptor names files through its discrete channel bits,
// so the OR of two descriptors flushes both files' output buffers in one call.
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

// §38.25 (C2): on failure the routine shall return nonzero, and the pending
// output is left untouched so nothing buffered is lost.
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

// §38.25 (C1): only the file(s) specified by the descriptor are flushed. With
// two channels holding pending output, flushing one descriptor commits that
// channel and leaves the other's buffer untouched.
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
  // The unnamed channel keeps its pending text and has flushed nothing.
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd_b), "keep-me");
  EXPECT_EQ(vpi_ctx_.McdChannelFlushed(mcd_b), "");
}

// §38.25 (C1, C2): flushing a descriptor whose file has no pending output is
// still a successful flush - there is simply nothing to commit, so the routine
// reports success and the committed stream stays empty.
TEST_F(VpiMcdFlushSim, FlushingDescriptorWithNoPendingOutputSucceeds) {
  char name[] = "quiet.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  // No WriteMcdChannel: the channel exists but its buffer is empty.
  EXPECT_EQ(vpi_mcd_flush(mcd), 0);
  EXPECT_EQ(vpi_ctx_.McdChannelFlushed(mcd), "");
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
}

}  // namespace
}  // namespace delta
