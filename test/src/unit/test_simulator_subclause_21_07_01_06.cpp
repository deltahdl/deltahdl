#include <algorithm>
#include <iostream>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "fixture_vcd_dump_run.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.1.6: reading the dump file during simulation with $dumpflush. The task
// empties the operating system's buffer for the VCD file so everything
// recorded so far is stored in the file, and afterwards dumping resumes as
// before with no value changes lost. Both faces are runtime rules whose
// observable is the file's on-disk contents WHILE the simulation still runs,
// so each test drives real source through parse, elaboration, lowering, and
// the scheduler with the driver's per-timestep recording loop installed, and
// plays the role of the LRM's "application program": procedural code in the
// design opens the dump file mid-run, echoes its current bytes to stdout
// between markers, and closes it again. The captured echo is the
// mid-simulation snapshot the assertions inspect alongside the final file --
// nothing is hand-driven on the writer and no previous values are seeded.
class DumpflushSysTask : public VcdMidRunReaderTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit),
  // capturing stdout produced during the run so mid-simulation reader
  // snippets can be inspected afterwards. Returns the final dump contents.
  std::string RunVcd(const std::string& src) {
    return RunVcdDump(src, {.captured_stdout = &run_output_});
  }
};

// The core rule, in the shape of the LRM's Example 1: after $dumpvars and a
// recorded change, executing $dumpflush stores all data buffered so far in
// the VCD file, where a reader running during the same simulation finds the
// header, the timestamp, and the value change already on disk.
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
  // Everything dumped before the flush is readable during the simulation.
  EXPECT_NE(mid.find("$enddefinitions"), std::string::npos);
  EXPECT_NE(mid.find("#10"), std::string::npos);
  EXPECT_NE(mid.find("b10100101 !"), std::string::npos);
  // The flush's own time unit has not been recorded yet at read time.
  EXPECT_EQ(mid.find("#20"), std::string::npos);
  // The final file retains the record: nothing was lost by flushing.
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

// Counterfactual twin of the test above with the $dumpflush removed: the
// records still sit in the stream buffer, so the mid-simulation reader finds
// an empty file -- it is the flush that stores the buffered data. The final
// file still holds the change once the writer closes, so nothing is lost
// either way; only the mid-run visibility differs.
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

// A flush in the same time unit as a change stores everything dumped so far,
// but that unit's own record follows at the end of the time unit -- and it is
// not lost: dumping resumes as before, so the record lands in the file.
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
  // The flush ran: the header is on disk...
  EXPECT_NE(mid.find("$enddefinitions"), std::string::npos);
  // ...but the current unit's change is dumped after the procedural code.
  EXPECT_EQ(mid.find("10100101"), std::string::npos);
  // No value change is lost: the record is in the final file.
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

// $dumpflush can be executed repeatedly: each flush stores everything dumped
// up to that moment, and the changes recorded between two flushes appear in
// the second snapshot -- dumping continued seamlessly in between.
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
  // First flush: the first change is on disk, the second has not happened.
  EXPECT_NE(mid1.find("b10100101 !"), std::string::npos);
  EXPECT_EQ(mid1.find("b1011010 !"), std::string::npos);
  // Second flush: both changes are on disk -- no value change was lost
  // between the flushes.
  EXPECT_NE(mid2.find("b10100101 !"), std::string::npos);
  EXPECT_NE(mid2.find("b1011010 !"), std::string::npos);
  EXPECT_NE(content.find("b1011010 !"), std::string::npos);
}

// After the flush, dumping resumes exactly as before: a later change is still
// recorded, and the flush itself writes no command into the dump file (it is
// neither a declaration nor a simulation command of the VCD format).
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
  EXPECT_NE(content.find("b1011010 !"), std::string::npos);  // post-flush
  EXPECT_EQ(content.find("$dumpflush"), std::string::npos);
}

// "Resumed as before" holds symmetrically for a suspended dump: with the dump
// suspended by §21.7.1.3's $dumpoff, $dumpflush still stores the buffered
// data (including the suspension checkpoint) in the file, yet leaves the dump
// suspended -- a change in the suspended window is not recorded as its own
// value change, and its value first surfaces in the $dumpon checkpoint.
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
  // The suspension checkpoint reached the disk through the flush.
  EXPECT_NE(MidDump("MID1").find("$dumpoff"), std::string::npos);
  // The flush did not resume the dump: the suspended-window value appears
  // only from the $dumpon checkpoint onward, never before it.
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  auto val = content.find("b1110111 !");
  ASSERT_NE(val, std::string::npos);
  EXPECT_LT(on, val);
}

// The task is an ordinary task enable: invoked from a task body, $dumpflush
// still stores the buffered data where the mid-simulation reader finds it.
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

// Input produced by the dependency idiom of §21.7.1.1/§21.7.1.2: $dumpflush
// at the end of the $dumpfile + $dumpvars sequence flushes the dump built by
// that sequence, and the file remains intact afterwards.
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

// Negative: with no dump file in place, executing $dumpflush is harmless --
// the design still runs to completion without errors.
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
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
}  // namespace delta
