#include <gtest/gtest.h>

#include <cstdarg>
#include <string>

#include "helpers_run_files.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

PLI_INT32 print_result = 0;

PLI_INT32 PrintThroughAList(PLI_UINT32 mcd, const char* format, ...) {
  va_list args{};
  va_start(args, format);
  const PLI_INT32 kCount = vpi_mcd_vprintf(mcd, VpiText(format), args);
  va_end(args);
  return kCount;
}

class VprintfInARun : public RunFilesRun {
 protected:
  void SetUp() override {
    RunFilesRun::SetUp();
    print_result = 0;
  }

  static PLI_INT32 PrintToAnFd(PLI_BYTE8*) {
    print_result = PrintThroughAList(DescriptorIn("top.fd"), "stray %d", 1);
    return 0;
  }

  static PLI_INT32 PrintToTheDesignsMcd(PLI_BYTE8*) {
    print_result = PrintThroughAList(DescriptorIn("top.mcd"), "design %d\n", 3);
    return 0;
  }

  static PLI_INT32 PrintToBothOpeners(PLI_BYTE8*) {
    const PLI_UINT32 kVpi = vpi_mcd_open(VpiText("v.txt"));
    print_result =
        PrintThroughAList(kVpi | DescriptorIn("top.mcd"), "both %d\n", 4);
    vpi_mcd_close(kVpi);
    return 0;
  }

  static PLI_INT32 PrintBeside(PLI_BYTE8*) {
    PrintThroughAList(DescriptorIn("top.mcd") << 1, "stray %d", 5);
    return 0;
  }
};

constexpr const char* kDesignMcd =
    "module top; integer mcd;\n"
    "  initial begin\n"
    "    mcd = $fopen(\"d.txt\");\n"
    "    $print;\n"
    "    $fclose(mcd);\n"
    "  end\n"
    "endmodule\n";

TEST_F(VprintfInARun, AnFdFromTheDesignIsNotWritten) {
  RegisterTask("$print", &PrintToAnFd);
  Run("module top; integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"fd.txt\", \"w\");\n"
      "    $print;\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FileText("fd.txt"), "");
}

TEST_F(VprintfInARun, TheDesignsMcdReceivesTheText) {
  RegisterTask("$print", &PrintToTheDesignsMcd);
  Run(kDesignMcd);
  EXPECT_EQ(print_result, 9);
  EXPECT_EQ(FileText("d.txt"), "design 3\n");
}

TEST_F(VprintfInARun, AVpiMcdOredWithTheDesignsWritesBothFiles) {
  RegisterTask("$print", &PrintToBothOpeners);
  Run(kDesignMcd);
  EXPECT_EQ(print_result, 7);
  EXPECT_EQ(FileText("d.txt"), "both 4\n");
  EXPECT_EQ(FileText("v.txt"), "both 4\n");
}

TEST_F(VprintfInARun, AChannelWithNoFileWritesNowhere) {
  RegisterTask("$print", &PrintBeside);
  Run(kDesignMcd);
  EXPECT_EQ(FileText("d.txt"), "");
}

}  // namespace
}  // namespace delta
