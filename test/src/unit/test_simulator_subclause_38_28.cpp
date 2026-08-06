#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiMcdPrintfSim : public ::testing::Test {
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

// §38.28: the descriptor names files through its discrete channel bits, so the
// OR of two mcd-opened descriptors writes the same text to both files in one
// call, and the routine returns the number of characters printed.
TEST_F(VpiMcdPrintfSim, WritesToSeveralChannelsSimultaneouslyAndReturnsCount) {
  char a[] = "a.log";
  char b[] = "b.log";
  PLI_UINT32 mcd_a = vpi_mcd_open(a);
  PLI_UINT32 mcd_b = vpi_mcd_open(b);
  ASSERT_NE(mcd_a, 0u);
  ASSERT_NE(mcd_b, 0u);

  char fmt[] = "hello";
  PLI_INT32 written = vpi_mcd_printf(mcd_a | mcd_b, fmt);

  EXPECT_EQ(written, 5);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd_a), "hello");
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd_b), "hello");
}

// §38.28: the text is controlled by a format string using the same format as
// the C fprintf() routine, and the return value counts the expanded characters.
TEST_F(VpiMcdPrintfSim, FormatStringControlsTheTextLikeCFprintf) {
  char name[] = "fmt.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  char fmt[] = "%d-%s";
  char arg[] = "ok";
  PLI_INT32 written = vpi_mcd_printf(mcd, fmt, 42, arg);

  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "42-ok");
  EXPECT_EQ(written, 5);
}

// §38.28: an error returns EOF. With no format string there is nothing to
// print, so the routine reports the error and writes nothing.
TEST_F(VpiMcdPrintfSim, ReturnsEofWhenFormatStringIsMissing) {
  char name[] = "err.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  EXPECT_EQ(vpi_mcd_printf(mcd, nullptr), EOF);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
}

// §38.28: the MSB of the descriptor names a file opened as an fd by $fopen, so
// a descriptor with only the MSB set writes to that fd-backed channel.
TEST_F(VpiMcdPrintfSim, WritesToAnFdFileViaTheMsbDescriptor) {
  PLI_UINT32 fd = PLI_UINT32{1} << 31;

  char fmt[] = "to fd";
  PLI_INT32 written = vpi_mcd_printf(fd, fmt);

  EXPECT_EQ(written, 5);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(fd), "to fd");
}

}  // namespace
}  // namespace delta
