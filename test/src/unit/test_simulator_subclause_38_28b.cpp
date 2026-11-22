#include <gtest/gtest.h>

#include <cstdio>
#include <filesystem>
#include <string>

#include "helpers_run_files.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

PLI_INT32 print_result = 0;

class PrintInARun : public RunFilesRun {
 protected:
  void SetUp() override {
    RunFilesRun::SetUp();
    print_result = 0;
  }

  static PLI_INT32 PrintToBothOpeners(PLI_BYTE8*) {
    const PLI_UINT32 kVpi = vpi_mcd_open(VpiText("v.txt"));
    print_result =
        vpi_mcd_printf(kVpi | DescriptorIn("top.mcd"), VpiText("both\n"));
    vpi_mcd_close(kVpi);
    return 0;
  }

  static PLI_INT32 PrintToAnFd(PLI_BYTE8*) {
    const PLI_UINT32 kVpi = vpi_mcd_open(VpiText("v.txt"));
    vpi_mcd_printf(DescriptorIn("top.fd"), VpiText("stray-fd"));
    vpi_mcd_close(kVpi);
    return 0;
  }

  static PLI_INT32 PrintOnChannelOne(PLI_BYTE8*) {
    print_result = vpi_mcd_printf(1u, VpiText("to the log\n"));
    return 0;
  }

  static PLI_INT32 PrintToAFullDevice(PLI_BYTE8*) {
    const PLI_UINT32 kMcd = vpi_mcd_open(VpiText("/dev/full"));
    print_result = vpi_mcd_printf(kMcd, VpiText("lost"));
    vpi_mcd_close(kMcd);
    return 0;
  }
};

TEST_F(PrintInARun, ADesignMcdOredWithAVpiMcdWritesBothFiles) {
  RegisterTask("$print", &PrintToBothOpeners);
  Run("module top; integer mcd;\n"
      "  initial begin\n"
      "    mcd = $fopen(\"d.txt\");\n"
      "    $print;\n"
      "    $fclose(mcd);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(print_result, 5);
  EXPECT_EQ(FileText("d.txt"), "both\n");
  EXPECT_EQ(FileText("v.txt"), "both\n");
}

TEST_F(PrintInARun, AnFdFromTheDesignIsWrittenNowhere) {
  RegisterTask("$print", &PrintToAnFd);
  testing::internal::CaptureStdout();
  Run("module top; integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"fd.txt\", \"w\");\n"
      "    $print;\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n");
  const std::string kOut = testing::internal::GetCapturedStdout();
  EXPECT_EQ(FileText("fd.txt"), "");
  EXPECT_EQ(FileText("v.txt"), "");
  EXPECT_EQ(kOut.find("stray-fd"), std::string::npos);
  EXPECT_EQ((vpi_.OutputChannelBuffer() + vpi_.OutputChannelFlushed() +
             vpi_.LogFileBuffer() + vpi_.LogFileFlushed())
                .find("stray-fd"),
            std::string::npos);
}

TEST_F(PrintInARun, ChannelOneReachesTheCurrentLogFile) {
  RegisterTask("$print", &PrintOnChannelOne);
  vpi_.ConnectOutputChannel(&f_.ctx.Log().Out());
  testing::internal::CaptureStdout();
  Run("module top; initial begin\n"
      "  $log(\"run.log\");\n"
      "  $display(\"before\"); $print; $display(\"after\");\n"
      "end endmodule\n");
  vpi_.ConnectOutputChannel(nullptr);
  const std::string kOut = testing::internal::GetCapturedStdout();
  EXPECT_EQ(print_result, 11);
  EXPECT_EQ(kOut, "before\nto the log\nafter\n");
  EXPECT_EQ(FileText("run.log"), "before\nto the log\nafter\n");
}

TEST_F(PrintInARun, DISABLED_AWriteTheFileRefusesReturnsEof) {
  if (!std::filesystem::exists("/dev/full")) GTEST_SKIP() << "no /dev/full";
  RegisterTask("$print", &PrintToAFullDevice);
  Run("module top; initial $print; endmodule\n");
  EXPECT_EQ(print_result, EOF);
}

}  // namespace
}  // namespace delta
