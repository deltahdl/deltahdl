#include <gtest/gtest.h>

#include <cstdio>
#include <string>

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

TEST_F(VpiMcdPrintfSim, ChannelOneAndAFileEachReceiveTheTextOnce) {
  char name[] = "f.log";
  const PLI_UINT32 kMcd = vpi_mcd_open(name);
  ASSERT_NE(kMcd, 0u);
  char fmt[] = "once\n";
  EXPECT_EQ(vpi_mcd_printf(1u | kMcd, fmt), 5);
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), "once\n");
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), "once\n");
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(kMcd), "once\n");
}

TEST_F(VpiMcdPrintfSim, OtherConversionsExpandLikeFprintf) {
  const PLI_UINT32 kMcd = vpi_mcd_open(VpiText("conv.log"));
  ASSERT_NE(kMcd, 0u);
  EXPECT_EQ(vpi_mcd_printf(kMcd, VpiText("%f|%e|%g|%c|%x|%o|%%"), 2.5, 2.5,
                           0.0001, 'z', 255, 8),
            38);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(kMcd),
            "2.500000|2.500000e+00|0.0001|z|ff|10|%");
}

TEST_F(VpiMcdPrintfSim, WidthPrecisionAndFlagsExpandLikeFprintf) {
  const PLI_UINT32 kMcd = vpi_mcd_open(VpiText("spec.log"));
  ASSERT_NE(kMcd, 0u);
  EXPECT_EQ(vpi_mcd_printf(kMcd, VpiText("[%5d][%-5s][%.3f][%08x][%+d][%*d]"),
                           42, "ab", 2.5, 0xbeef, -7, 4, 9),
            41);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(kMcd),
            "[   42][ab   ][2.500][0000beef][-7][   9]");
}

TEST_F(VpiMcdPrintfSim, AnEmptyFormatWritesNothingAndReturnsZero) {
  const PLI_UINT32 kMcd = vpi_mcd_open(VpiText("empty.log"));
  ASSERT_NE(kMcd, 0u);
  EXPECT_EQ(vpi_mcd_printf(kMcd, VpiText("")), 0);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(kMcd), "");
}

TEST_F(VpiMcdPrintfSim, TheHighestChannelReceivesTheText) {
  PLI_UINT32 last = 0;
  for (int i = 0; i < 30; ++i) {
    const std::string kName = "c" + std::to_string(i) + ".log";
    last = vpi_mcd_open(VpiText(kName.c_str()));
  }
  ASSERT_EQ(last, PLI_UINT32{1} << 30);
  char fmt[] = "top";
  EXPECT_EQ(vpi_mcd_printf(last, fmt), 3);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(last), "top");
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), "");
}

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

TEST_F(VpiMcdPrintfSim, ReturnsEofWhenFormatStringIsMissing) {
  char name[] = "err.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  EXPECT_EQ(vpi_mcd_printf(mcd, nullptr), EOF);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
}

TEST_F(VpiMcdPrintfSim, WritesNothingToAFileNamedByAnFdDescriptor) {
  PLI_UINT32 fd = PLI_UINT32{1} << 31;

  char fmt[] = "to fd";
  PLI_INT32 written = vpi_mcd_printf(fd, fmt);

  EXPECT_EQ(written, 0);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(fd), "");
}

TEST_F(VpiMcdPrintfSim, AnFdWritesNoneOfTheChannelsItsLowerBitsWouldName) {
  char name[] = "overlap.log";
  PLI_UINT32 mcd = vpi_mcd_open(name);
  ASSERT_NE(mcd, 0u);

  PLI_UINT32 fd = (PLI_UINT32{1} << 31) | 1u | mcd;
  char fmt[] = "unwritten";
  PLI_INT32 written = vpi_mcd_printf(fd, fmt);

  EXPECT_EQ(written, 0);
  EXPECT_EQ(vpi_ctx_.McdChannelBuffer(mcd), "");
  EXPECT_EQ(vpi_ctx_.OutputChannelBuffer(), "");
  EXPECT_EQ(vpi_ctx_.LogFileBuffer(), "");
}

class PrintOnARunChannel : public RunFilesRun {
 protected:
  static PLI_INT32 PrintBeside(PLI_BYTE8*) {
    vpi_mcd_printf(DescriptorIn("top.mcd") << 1, VpiText("stray"));
    return 0;
  }
};

TEST_F(PrintOnARunChannel, AChannelWithNoFileWritesNowhere) {
  RegisterTask("$print_beside", &PrintBeside);
  Run("module top; integer mcd;\n"
      "  initial begin\n"
      "    mcd = $fopen(\"kept.txt\");\n"
      "    $print_beside;\n"
      "    $fclose(mcd);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FileText("kept.txt"), "");
}

}  // namespace
}  // namespace delta
