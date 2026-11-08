#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class DumpflushSysTask : public VcdMidRunReaderTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    return RunVcdDump(src, {.captured_stdout = &run_output_});
  }
};

TEST_F(DumpflushSysTask, FlushStoresBufferedDataInFileMidSimulation) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  integer rfd;\n"
      "  integer rch;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'hA5;\n"
      "    #10 begin\n"
      "      $dumpflush;\n" +
      ReaderSnippet("MID1") +
      "    end\n"
      "  end\n"
      "endmodule\n");
  auto mid = MidDump("MID1");
  EXPECT_NE(mid.find("$enddefinitions"), std::string::npos);
  EXPECT_NE(mid.find("#10"), std::string::npos);
  EXPECT_NE(mid.find("b10100101 !"), std::string::npos);
  EXPECT_EQ(mid.find("#20"), std::string::npos);
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

TEST_F(DumpflushSysTask, WithoutFlushBufferedDataNotYetInFile) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  integer rfd;\n"
      "  integer rch;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'hA5;\n"
      "    #10 begin\n" +
      ReaderSnippet("MID1") +
      "    end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(MidDump("MID1"), "");
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

TEST_F(DumpflushSysTask, FlushInChangeUnitPrecedesThatUnitsRecord) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  integer rfd;\n"
      "  integer rch;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 begin\n"
      "      data = 8'hA5;\n"
      "      $dumpflush;\n" +
      ReaderSnippet("MID1") +
      "    end\n"
      "  end\n"
      "endmodule\n");
  auto mid = MidDump("MID1");
  EXPECT_NE(mid.find("$enddefinitions"), std::string::npos);
  EXPECT_EQ(mid.find("10100101"), std::string::npos);
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

TEST_F(DumpflushSysTask, RepeatedFlushesEachStoreEverythingSoFar) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  integer rfd;\n"
      "  integer rch;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'hA5;\n"
      "    #5 begin\n"
      "      $dumpflush;\n" +
      ReaderSnippet("MID1") +
      "    end\n"
      "    #5 data = 8'h5A;\n"
      "    #5 begin\n"
      "      $dumpflush;\n" +
      ReaderSnippet("MID2") +
      "    end\n"
      "  end\n"
      "endmodule\n");
  auto mid1 = MidDump("MID1");
  auto mid2 = MidDump("MID2");
  EXPECT_NE(mid1.find("b10100101 !"), std::string::npos);
  EXPECT_EQ(mid1.find("b1011010 !"), std::string::npos);
  EXPECT_NE(mid2.find("b10100101 !"), std::string::npos);
  EXPECT_NE(mid2.find("b1011010 !"), std::string::npos);
  EXPECT_NE(content.find("b1011010 !"), std::string::npos);
}

TEST_F(DumpflushSysTask, DumpingContinuesAfterFlushAndNoCommandIsEmitted) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'hA5;\n"
      "    #10 $dumpflush;\n"
      "    #10 data = 8'h5A;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
  EXPECT_NE(content.find("b1011010 !"), std::string::npos);
  EXPECT_EQ(content.find("$dumpflush"), std::string::npos);
}

TEST_F(DumpflushSysTask, FlushWhileSuspendedLeavesDumpSuspended) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  integer rfd;\n"
      "  integer rch;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'hA5;\n"
      "    #5 $dumpoff;\n"
      "    #5 begin\n"
      "      $dumpflush;\n" +
      ReaderSnippet("MID1") +
      "    end\n"
      "    #5 data = 8'h77;\n"
      "    #5 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(MidDump("MID1").find("$dumpoff"), std::string::npos);
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  auto val = content.find("b1110111 !");
  ASSERT_NE(val, std::string::npos);
  EXPECT_LT(on, val);
}

TEST_F(DumpflushSysTask, FlushInvokedFromTaskBodyStoresBufferedData) {
  RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  integer rfd;\n"
      "  integer rch;\n"
      "  task flush_and_read;\n"
      "    $dumpflush;\n" +
      ReaderSnippet("MID1") +
      "  endtask\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'hA5;\n"
      "    #10 flush_and_read;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(MidDump("MID1").find("b10100101 !"), std::string::npos);
}

TEST_F(DumpflushSysTask, FlushAfterDumpfileAndDumpvarsSequence) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  integer rfd;\n"
      "  integer rch;\n"
      "  initial begin\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'hA5;\n"
      "    #10 begin\n"
      "      $dumpflush;\n" +
      ReaderSnippet("MID1") +
      "    end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(MidDump("MID1").find("b10100101 !"), std::string::npos);
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

TEST_F(DumpflushSysTask, WithoutDumpFileFlushIsHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #10 $dumpflush;\n"
      "    #10 data = 8'h22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.Vcd().GetVcdWriter(), nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
}  // namespace delta
