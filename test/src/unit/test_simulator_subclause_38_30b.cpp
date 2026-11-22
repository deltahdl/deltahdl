#include <gtest/gtest.h>

#include <string>

#include "helpers_run_files.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PrintfInARun : public RunFilesRun {
 protected:
  static PLI_INT32 PrintALine(PLI_BYTE8*) {
    vpi_printf(VpiText("printed %d\n"), 5);
    return 0;
  }
};

TEST_F(PrintfInARun, TheTextReachesTheCurrentLogFileInOrder) {
  RegisterTask("$print", &PrintALine);
  vpi_.ConnectOutputChannel(&f_.ctx.Log().Out());
  testing::internal::CaptureStdout();
  Run("module top; initial begin\n"
      "  $log(\"run.log\");\n"
      "  $display(\"before\"); $print; $display(\"after\");\n"
      "end endmodule\n");
  vpi_.ConnectOutputChannel(nullptr);
  const std::string kOut = testing::internal::GetCapturedStdout();
  EXPECT_EQ(kOut, "before\nprinted 5\nafter\n");
  EXPECT_EQ(FileText("run.log"), "before\nprinted 5\nafter\n");
}

}  // namespace
}  // namespace delta
