#include <gtest/gtest.h>

#include <cstdio>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiPrintfSim : public ::testing::Test {
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

// §38.30: vpi_printf() shall write to both the output channel of the tool and
// the current tool log file, expanding the C printf()-style format string with
// its variable arguments, and shall return the number of characters printed.
// One call exercises the conjunction (both destinations), the format expansion,
// and the character count together.
TEST_F(VpiPrintfSim,
       WritesExpandedTextToOutputChannelAndLogFileReturningCount) {
  PLI_BYTE8 format[] = "value=%d name=%s";
  int written = vpi_printf(format, 42, "ok");

  const std::string kExpected = "value=42 name=ok";
  // The same expanded text reached both the output channel and the log file.
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), kExpected);
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), kExpected);
  // The return value is the number of characters printed.
  EXPECT_EQ(written, static_cast<int>(kExpected.size()));
}

// §38.30: a missing format string names nothing to print, so the routine
// reports the error by returning EOF and writes to neither destination.
TEST_F(VpiPrintfSim, ReturnsEofWhenFormatStringIsMissing) {
  EXPECT_EQ(vpi_printf(nullptr), EOF);

  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
}

// §38.30 edge: an empty format expands to zero characters. The character count
// is independent of the (empty) write, so the routine returns 0 while still
// targeting both destinations - the boundary where the format pass is skipped.
TEST_F(VpiPrintfSim, EmptyFormatWritesNothingAndReturnsZero) {
  PLI_BYTE8 format[] = "";
  int written = vpi_printf(format);

  EXPECT_EQ(written, 0);
  EXPECT_TRUE(vpi_ctx_.OutputChannelBuffer().empty());
  EXPECT_TRUE(vpi_ctx_.LogFileBuffer().empty());
}

}  // namespace
}  // namespace delta
