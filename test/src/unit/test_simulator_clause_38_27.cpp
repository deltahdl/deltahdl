#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiMcdOpenSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Counts the set bits of an mcd; a freshly opened descriptor names exactly one
  // channel.
  static int ChannelCount(PLI_UINT32 mcd) {
    int n = 0;
    for (PLI_UINT32 m = mcd; m != 0; m &= m - 1) ++n;
    return n;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;

  // mcd channel 1 is the LSB, channel 32 is the MSB.
  static constexpr PLI_UINT32 kLsbChannel = 0x00000001u;
  static constexpr PLI_UINT32 kMsbChannel = 0x80000000u;
};

// §38.27: vpi_mcd_open() shall open a file for writing and return a
// corresponding multichannel descriptor. The descriptor is nonzero and the file
// is recorded as open under that descriptor.
TEST_F(VpiMcdOpenSim, OpensFileForWritingAndReturnsMcd) {
  char name[] = "trace.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);

  EXPECT_NE(mcd, 0u);
  EXPECT_TRUE(vpi_ctx_.IsMcdFileOpen("trace.log"));
  EXPECT_EQ(vpi_ctx_.McdForFile("trace.log"), mcd);
}

// §38.27: channel 1 (LSB) is reserved for the tool's output channel and log
// file, and channel 32 (MSB) is reserved for an fd from $fopen, so a fresh mcd
// never selects either. Each open names exactly one channel and distinct files
// receive distinct channels.
TEST_F(VpiMcdOpenSim, FreshDescriptorsAvoidReservedLsbAndMsbChannels) {
  char a[] = "a.txt";
  char b[] = "b.txt";
  PLI_UINT32 mcd_a = vpi_mcd_open(a);
  PLI_UINT32 mcd_b = vpi_mcd_open(b);

  for (PLI_UINT32 mcd : {mcd_a, mcd_b}) {
    EXPECT_EQ(ChannelCount(mcd), 1);
    EXPECT_EQ(mcd & kLsbChannel, 0u);
    EXPECT_EQ(mcd & kMsbChannel, 0u);
  }
  EXPECT_NE(mcd_a, mcd_b);
}

// §38.27: vpi_mcd_open() shall return 0 on error. An open that cannot be carried
// out and a missing file name both take the error return, and nothing is
// recorded.
TEST_F(VpiMcdOpenSim, ReturnsZeroOnError) {
  vpi_ctx_.SetMcdOpenShouldFail(true);
  char name[] = "denied.log";
  EXPECT_EQ(vpi_mcd_open(name), 0u);
  EXPECT_FALSE(vpi_ctx_.IsMcdFileOpen("denied.log"));

  EXPECT_EQ(vpi_mcd_open(nullptr), 0u);
}

// §38.27: if the file has already been opened by a previous vpi_mcd_open(), the
// routine shall return that same descriptor without consuming another channel.
TEST_F(VpiMcdOpenSim, ReopeningSameFileReturnsExistingDescriptor) {
  char name[] = "shared.log";
  PLI_UINT32 first = vpi_mcd_open(name);
  ASSERT_NE(first, 0u);

  PLI_UINT32 second = vpi_mcd_open(name);
  EXPECT_EQ(second, first);

  // A third, different file gets a new channel - re-opening did not consume one.
  char other[] = "other.log";
  PLI_UINT32 third = vpi_mcd_open(other);
  EXPECT_NE(third, first);
  EXPECT_EQ(ChannelCount(third), 1);
}

// §38.27: the mcd namespace is shared with $fopen, so a file already opened by
// $fopen is reported on its existing descriptor rather than a new one - the
// descriptors are compatible.
TEST_F(VpiMcdOpenSim, FileOpenedByFopenSharesDescriptorNamespace) {
  PLI_UINT32 fopen_mcd = 0x00000004u;  // channel 3, as $fopen might have chosen
  vpi_ctx_.RegisterFopenMcdFile("from_fopen.log", fopen_mcd);

  char name[] = "from_fopen.log";
  EXPECT_EQ(vpi_mcd_open(name), fopen_mcd);

  // A new file opened afterwards must not collide with the $fopen channel.
  char fresh[] = "fresh.log";
  PLI_UINT32 mcd = vpi_mcd_open(fresh);
  EXPECT_EQ(mcd & fopen_mcd, 0u);
}

// §38.27: only channels 2..31 are available (channels 1 and 32 are reserved), so
// once all are in use a further open has no free channel and returns 0.
TEST_F(VpiMcdOpenSim, ExhaustedChannelsReturnZero) {
  PLI_UINT32 used = 0;
  for (int i = 0; i < 30; ++i) {
    std::string name = "file" + std::to_string(i) + ".log";
    PLI_UINT32 mcd = vpi_mcd_open(name.data());
    ASSERT_NE(mcd, 0u) << "channel " << i << " should have been available";
    EXPECT_EQ(used & mcd, 0u);  // each open takes a distinct channel
    used |= mcd;
  }

  char overflow[] = "overflow.log";
  EXPECT_EQ(vpi_mcd_open(overflow), 0u);
}

}  // namespace
}  // namespace delta
