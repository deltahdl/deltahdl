#include <gtest/gtest.h>

#include <string>

#include "helpers_run_files.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr PLI_UINT32 kNoFileChannel = PLI_UINT32{1} << 20;

struct CloseResults {
  PLI_UINT32 first = 1;
  PLI_UINT32 second = 1;
  PLI_UINT32 third = 1;
  PLI_UINT32 opened = 0;
};

CloseResults results;

class McdCloseInARun : public RunFilesRun {
 protected:
  void SetUp() override {
    RunFilesRun::SetUp();
    results = {};
  }

  static PLI_UINT32 OpenAndPrint(const char* name) {
    const PLI_UINT32 kMcd = vpi_mcd_open(VpiText(name));
    vpi_mcd_printf(kMcd, VpiText("before\n"));
    return kMcd;
  }

  static PLI_INT32 CloseThenWrite(PLI_BYTE8*) {
    const PLI_UINT32 kMcd = OpenAndPrint("v.txt");
    results.first = vpi_mcd_close(kMcd);
    vpi_mcd_printf(kMcd, VpiText("after\n"));
    results.second = vpi_mcd_close(0u);
    return 0;
  }

  static PLI_INT32 CloseWithTheDesignsChannel(PLI_BYTE8*) {
    const PLI_UINT32 kMcd = OpenAndPrint("v.txt");
    results.first = vpi_mcd_close(kMcd | DescriptorIn("top.mcd"));
    vpi_mcd_printf(kMcd, VpiText("after\n"));
    return 0;
  }

  static PLI_INT32 CloseWithChannelOne(PLI_BYTE8*) {
    results.first = vpi_mcd_close(1u);
    const PLI_UINT32 kMcd = OpenAndPrint("v.txt");
    results.second = vpi_mcd_close(kMcd | 1u);
    vpi_mcd_printf(1u, VpiText("one-after\n"));
    return 0;
  }

  static PLI_INT32 CloseWithAChannelWithoutAFile(PLI_BYTE8*) {
    const PLI_UINT32 kMcd = OpenAndPrint("v.txt");
    results.first = vpi_mcd_close(kMcd | kNoFileChannel);
    vpi_mcd_printf(kMcd, VpiText("after\n"));
    return 0;
  }

  static PLI_INT32 CloseWhatIsAlreadyClosed(PLI_BYTE8*) {
    results.first = vpi_mcd_close(DescriptorIn("top.fd"));
    results.second = vpi_mcd_close(DescriptorIn("top.mcd"));
    results.opened = OpenAndPrint("v.txt");
    vpi_mcd_close(results.opened);
    results.third = vpi_mcd_close(results.opened);
    return 0;
  }
};

TEST_F(McdCloseInARun, AWriteAfterTheCloseAddsNothing) {
  RegisterTask("$close", &CloseThenWrite);
  Run("module top; initial $close; endmodule\n");
  EXPECT_EQ(results.first, 0u);
  EXPECT_EQ(FileText("v.txt"), "before\n");
}

TEST_F(McdCloseInARun, AnEmptyDescriptorLeavesNothingUnclosed) {
  RegisterTask("$close", &CloseThenWrite);
  Run("module top; initial $close; endmodule\n");
  EXPECT_EQ(results.second, 0u);
}

TEST_F(McdCloseInARun, OneCallClosesAVpiChannelAndADesignChannel) {
  RegisterTask("$close", &CloseWithTheDesignsChannel);
  Run("module top; integer mcd;\n"
      "  initial begin\n"
      "    mcd = $fopen(\"d.txt\");\n"
      "    $fdisplay(mcd, \"before\");\n"
      "    $close;\n"
      "    $fdisplay(mcd, \"after\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(results.first, 0u);
  EXPECT_EQ(FileText("v.txt"), "before\n");
  EXPECT_EQ(FileText("d.txt"), "before\n");
}

TEST_F(McdCloseInARun, ChannelOneStaysOpenAndWorking) {
  RegisterTask("$close", &CloseWithChannelOne);
  testing::internal::CaptureStdout();
  Run("module top; initial begin $close; $display(\"display-after\"); end\n"
      "endmodule\n");
  const std::string kOut = testing::internal::GetCapturedStdout();
  EXPECT_EQ(results.first, 1u);
  EXPECT_EQ(results.second, 1u);
  EXPECT_EQ(FileText("v.txt"), "before\n");
  EXPECT_NE(kOut.find("display-after"), std::string::npos);
  EXPECT_NE((vpi_.OutputChannelBuffer() + vpi_.OutputChannelFlushed())
                .find("one-after"),
            std::string::npos);
  EXPECT_NE((vpi_.LogFileBuffer() + vpi_.LogFileFlushed()).find("one-after"),
            std::string::npos);
}

TEST_F(McdCloseInARun, OnlyTheChannelWithoutAFileComesBack) {
  RegisterTask("$close", &CloseWithAChannelWithoutAFile);
  Run("module top; initial $close; endmodule\n");
  EXPECT_EQ(results.first, kNoFileChannel);
  EXPECT_EQ(FileText("v.txt"), "before\n");
}

TEST_F(McdCloseInARun, AChannelAlreadyClosedComesBack) {
  RegisterTask("$close", &CloseWhatIsAlreadyClosed);
  Run("module top; integer fd, mcd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"fd.txt\", \"w\");\n"
      "    mcd = $fopen(\"mcd.txt\");\n"
      "    $fclose(fd);\n"
      "    $fclose(mcd);\n"
      "    $close;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(results.opened, 0u);
  EXPECT_EQ(results.first, DescriptorIn("top.fd"));
  EXPECT_EQ(results.second, DescriptorIn("top.mcd"));
  EXPECT_EQ(results.third, results.opened);
}

}  // namespace
}  // namespace delta
