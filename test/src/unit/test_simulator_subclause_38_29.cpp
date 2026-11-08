#include <gtest/gtest.h>

#include <cstdarg>
#include <cstdio>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

PLI_INT32 CallWithStartedVarargs(PLI_UINT32 mcd, const char* format, ...) {
  va_list ap;
  va_start(ap, format);
  PLI_INT32 written = vpi_mcd_vprintf(mcd, const_cast<PLI_BYTE8*>(format), ap);
  va_end(ap);
  return written;
}

class VpiMcdVprintfSim : public ::testing::Test {
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

TEST_F(VpiMcdVprintfSim,
       ConsumesAnAlreadyStartedVarargsListAndWritesFormattedText) {
  char name[] = "v.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  char arg[] = "ok";
  PLI_INT32 written = CallWithStartedVarargs(mcd, "%d-%s", 42, arg);

  EXPECT_EQ(written, 5);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "42-ok");
}

TEST_F(VpiMcdVprintfSim, WritesToEveryChannelNamedByTheDescriptor) {
  char first[] = "v1.log";
  char second[] = "v2.log";
  PLI_UINT32 mcd1 = vpi_mcd_open(first);
  PLI_UINT32 mcd2 = vpi_mcd_open(second);
  ASSERT_NE(mcd1, 0u);
  ASSERT_NE(mcd2, 0u);
  ASSERT_NE(mcd1, mcd2);

  PLI_INT32 written = CallWithStartedVarargs(mcd1 | mcd2, "x=%d", 7);

  EXPECT_EQ(written, 3);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd1), "x=7");
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd2), "x=7");
}

TEST_F(VpiMcdVprintfSim, ReturnsEofWhenFormatStringIsMissing) {
  char name[] = "verr.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  EXPECT_EQ(CallWithStartedVarargs(mcd, nullptr), EOF);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
}

TEST_F(VpiMcdVprintfSim, EmptyFormatStringWritesNothingAndReturnsZero) {
  char name[] = "vempty.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  PLI_INT32 written = CallWithStartedVarargs(mcd, "");

  EXPECT_EQ(written, 0);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
}

TEST_F(VpiMcdVprintfSim, WritesNothingWhereTheDescriptorIsAnFdFromFopen) {
  char opened[] = "vfd.log";
  PLI_UINT32 covered = vpi_mcd_open(opened);
  ASSERT_NE(covered, 0u);

  PLI_INT32 written =
      CallWithStartedVarargs((PLI_UINT32{1} << 31) | 1u | covered, "n=%d", 9);

  EXPECT_EQ(written, 0);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(covered), "");
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), "");
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), "");
}

}  // namespace
}  // namespace delta
