#include <gtest/gtest.h>

#include <cstdarg>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// Helper that mirrors how a PLI application would forward an already-started
// varargs list to vpi_mcd_vprintf(): it starts the list with va_start and hands
// the live va_list to the routine under test, which is the distinguishing trait
// of §38.29 versus vpi_mcd_printf() (§38.28).
PLI_INT32 CallWithStartedVarargs(PLI_UINT32 mcd, const char* format, ...) {
  va_list ap;
  va_start(ap, format);
  PLI_INT32 written =
      vpi_mcd_vprintf(mcd, const_cast<PLI_BYTE8*>(format), ap);
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

// §38.29: the routine performs the same function as vpi_mcd_printf() but on an
// already-started varargs list. Forwarding a live va_list expands the C
// fprintf()-style format against the caller's arguments, writes the result to
// the channel named by the descriptor, and returns the number of characters
// written.
TEST_F(VpiMcdVprintfSim, ConsumesAnAlreadyStartedVarargsListAndWritesFormattedText) {
  char name[] = "v.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  char arg[] = "ok";
  PLI_INT32 written = CallWithStartedVarargs(mcd, "%d-%s", 42, arg);

  EXPECT_EQ(written, 5);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "42-ok");
}

// §38.29: an error returns EOF. With no format string there is nothing to
// print, so the routine reports the error and writes nothing - exercising the
// error branch of the va_list-taking entry point itself.
TEST_F(VpiMcdVprintfSim, ReturnsEofWhenFormatStringIsMissing) {
  char name[] = "verr.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  EXPECT_EQ(CallWithStartedVarargs(mcd, nullptr), EOF);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
}

// §38.29: an empty format string is not an error - it expands to zero
// characters. The routine still completes against the started varargs list,
// writes nothing to the channel, and returns a count of zero (exercising the
// path where the formatted length is zero).
TEST_F(VpiMcdVprintfSim, EmptyFormatStringWritesNothingAndReturnsZero) {
  char name[] = "vempty.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  PLI_INT32 written = CallWithStartedVarargs(mcd, "");

  EXPECT_EQ(written, 0);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
}

}  // namespace
}  // namespace delta
