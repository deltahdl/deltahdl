#include <gtest/gtest.h>

#include <cstdarg>
#include <cstdio>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// Helper that mirrors how a PLI application would forward an already-started
// varargs list to vpi_vprintf(): it starts the list with va_start and hands the
// live va_list to the routine under test, which is the distinguishing trait of
// §38.41 versus vpi_printf() (§38.30).
PLI_INT32 CallWithStartedVarargs(const char* format, ...) {
  va_list ap;
  va_start(ap, format);
  PLI_INT32 written = vpi_vprintf(const_cast<PLI_BYTE8*>(format), ap);
  va_end(ap);
  return written;
}

class VpiVprintfSim : public ::testing::Test {
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

// §38.41: the routine performs the same function as vpi_printf() but on an
// already-started varargs list. Forwarding a live va_list expands the C
// printf()-style format against the caller's arguments, writes the result to
// both the tool's output channel and the current tool log file, and returns the
// number of characters written. One call exercises that conjunction together.
TEST_F(VpiVprintfSim,
       ConsumesAnAlreadyStartedVarargsListWritingBothDestinations) {
  PLI_INT32 written = CallWithStartedVarargs("value=%d name=%s", 42, "ok");

  const std::string expected = "value=42 name=ok";
  // The same expanded text reached both the output channel and the log file.
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), expected);
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), expected);
  // The return value is the number of characters written.
  EXPECT_EQ(written, static_cast<PLI_INT32>(expected.size()));
}

// §38.41: an error returns EOF. With no format string there is nothing to
// print, so the routine reports the error and writes to neither destination -
// exercising the error branch of the va_list-taking entry point itself.
TEST_F(VpiVprintfSim, ReturnsEofWhenFormatStringIsMissing) {
  EXPECT_EQ(CallWithStartedVarargs(nullptr), EOF);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
}

// §38.41 edge: an empty format string is not an error - it expands to zero
// characters. The routine still completes against the started varargs list,
// writes nothing to either destination, and returns a count of zero (the
// boundary where the format pass is skipped).
TEST_F(VpiVprintfSim, EmptyFormatStringWritesNothingAndReturnsZero) {
  PLI_INT32 written = CallWithStartedVarargs("");

  EXPECT_EQ(written, 0);
  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
}

}  // namespace
}  // namespace delta
