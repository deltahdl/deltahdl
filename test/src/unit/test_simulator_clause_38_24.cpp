#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

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

  // mcd channel 1 is the LSB - the predefined output/log descriptor.
  static constexpr PLI_UINT32 kLsbChannel = 0x00000001u;
};

// §38.24 (C1, C3): vpi_mcd_close() shall close the file named by the descriptor
// and return 0 on success. After the close the file is no longer open and its
// channel is free again.
TEST_F(VpiMcdCloseSim, ClosesFileAndReturnsZeroOnSuccess) {
  char name[] = "trace.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);
  ASSERT_TRUE(vpi_ctx_.IsMcdFileOpen("trace.log"));

  EXPECT_EQ(vpi_mcd_close(mcd), 0u);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("trace.log"));

  // The freed channel is handed out again by a later open.
  char again[] = "again.log";
  EXPECT_EQ(vpi_mcd_open(again), mcd);
}

// §38.24 (C2): channels are discrete bits of the mcd, so a single call closes
// several channels at once. Passing the OR of two descriptors closes both
// files.
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

// §38.24 (C4): on error the routine shall return the mcd of the unclosed
// channels. A bit naming no open channel cannot be closed, so it is returned;
// the channels that were open in the same call are still closed.
TEST_F(VpiMcdCloseSim, ReturnsUnclosedChannelsOnError) {
  char name[] = "open.log";
  PLI_UINT32 open_mcd = vpi_mcd_open(name);
  ASSERT_NE(open_mcd, 0u);

  // Pick a channel bit that is not currently allocated to anything.
  PLI_UINT32 stale = (open_mcd == 0x40000000u) ? 0x20000000u : 0x40000000u;
  ASSERT_EQ(open_mcd & stale, 0u);

  // Close the live channel together with the stale one: only the stale bit is
  // reported back as unclosed.
  EXPECT_EQ(vpi_mcd_close(open_mcd | stale), stale);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("open.log"));
}

// §38.24 (C6): descriptor 1 (the LSB) is predefined for the tool's output
// channel and current log file and cannot be closed. It is reported back as an
// unclosed channel.
TEST_F(VpiMcdCloseSim, PredefinedDescriptorOneCannotBeClosed) {
  EXPECT_EQ(vpi_mcd_close(kLsbChannel), kLsbChannel);

  // Even bundled with a real channel, the LSB survives while the real one
  // closes.
  char name[] = "real.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);
  EXPECT_EQ(vpi_mcd_close(mcd | kLsbChannel), kLsbChannel);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("real.log"));
}

// §38.24 (C2, C4): a single call may name channels that cannot be closed for
// different reasons - the reserved descriptor 1 and a bit naming no open
// channel
// - alongside one that can. The live channel is closed and the returned mcd is
// the OR of every channel left open, regardless of why each was left open.
TEST_F(VpiMcdCloseSim, ReportsAllUnclosedChannelsWhileClosingTheRest) {
  char name[] = "live.log";
  PLI_UINT32 live = vpi_mcd_open(name);
  ASSERT_NE(live, 0u);

  // A high channel bit that is not allocated to anything and differs from live.
  PLI_UINT32 stale = (live == 0x40000000u) ? 0x20000000u : 0x40000000u;
  ASSERT_EQ(live & stale, 0u);

  PLI_UINT32 result = vpi_mcd_close(live | stale | kLsbChannel);
  EXPECT_EQ(result, stale | kLsbChannel);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("live.log"));
}

// §38.24 (C5): the mcd namespace is shared with $fopen (§21.3.1), so a
// descriptor opened by $fopen can be closed here. After closing, its channel is
// free.
TEST_F(VpiMcdCloseSim, ClosesDescriptorOpenedByFopen) {
  PLI_UINT32 fopen_mcd = 0x00000004u;  // channel 3, as $fopen might have chosen
  vpi_ctx_.RegisterFopenMcdFile("from_fopen.log", fopen_mcd);
  ASSERT_TRUE(vpi_ctx_.IsMcdFileOpen("from_fopen.log"));

  EXPECT_EQ(vpi_mcd_close(fopen_mcd), 0u);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("from_fopen.log"));

  // The freed channel can be reused by a fresh open.
  char fresh[] = "fresh.log";
  EXPECT_EQ(vpi_mcd_open(fresh), fopen_mcd);
}

}  // namespace
}  // namespace delta
