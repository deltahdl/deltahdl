#include <gtest/gtest.h>

#include <fstream>
#include <ios>
#include <iterator>
#include <string>

#include "fixture_vpi_run.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::string log_path;
std::string log_seen_after_flush;
PLI_INT32 flush_result = -1;

std::string ContentsOf(const std::string& path) {
  std::ifstream in(path, std::ios::binary);
  return {std::istreambuf_iterator<char>(in), std::istreambuf_iterator<char>()};
}

PLI_INT32 PrintThenFlushCalltf(PLI_BYTE8*) {
  vpi_printf(VpiText("flushed text\n"));
  flush_result = vpi_flush();
  log_seen_after_flush = ContentsOf(log_path);
  return 0;
}

class FlushOfARun : public VpiDesignRun {
 protected:
  std::string StdoutOfAFlushingRun() {
    log_path = testing::TempDir() + "vpi_flush_run.log";
    log_seen_after_flush.clear();
    flush_result = -1;
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = &PrintThenFlushCalltf;
    EXPECT_NE(vpi_register_systf(&data), nullptr);
    vpi_.ConnectOutputChannel(&f_.ctx.Log().Out());
    testing::internal::CaptureStdout();
    Run("module top; initial begin\n"
        "  $log(\"" +
        log_path +
        "\");\n"
        "  $display(\"before\"); $probe; $display(\"after\");\n"
        "end endmodule\n");
    vpi_.ConnectOutputChannel(nullptr);
    return testing::internal::GetCapturedStdout();
  }
};

TEST_F(FlushOfARun, FlushedTextReachesTheOutputChannel) {
  EXPECT_EQ(StdoutOfAFlushingRun(), "before\nflushed text\nafter\n");
  EXPECT_EQ(flush_result, 0);
}

TEST_F(FlushOfARun, FlushedTextIsInTheCurrentLogFileWhenTheFlushReturns) {
  StdoutOfAFlushingRun();
  EXPECT_EQ(flush_result, 0);
  EXPECT_EQ(log_seen_after_flush, "before\nflushed text\n");
}

}  // namespace
}  // namespace delta
