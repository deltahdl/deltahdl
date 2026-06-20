#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_buffered_dump.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Drives the $dumpportsflush system task end to end so the extended-VCD
// buffer-flushing semantics of §21.7.3.5 are observed as the production task
// path applies them. The flush reuses the buffer-flushing machinery the
// extended VCD file inherits (§21.7.1.6).
class DumpportsflushSysTask : public VcdTestBase {};

// §21.7.3.5 C2/C3: $dumpportsflush writes the buffered port values out to the
// associated file, clearing the simulator's VCD buffer so a reader sees them
// while the simulation is still running. Issued with no filename, the SHALL is
// to flush the buffers for every file opened by $dumpports; with this
// single-file writer that empties the one dump. The named form
// $dumpportsflush("ports.vcd") dispatches identically through the single
// writer, so it is covered by the same production branch. Before the flush the
// value records sit buffered and are not yet in the file; after the production
// path runs they are.
TEST_F(DumpportsflushSysTask, FlushesBufferedPortValues) {
  SimFixture f;
  VcdWriter vcd(tmp_path_);
  SetupBufferedVcdDump(f, vcd, ReadVcd());

  EvalExpr(MkSysCall(f.arena, "$dumpportsflush", {}), f.ctx, f.arena);

  // After the flush the file reflects everything dumped so far, and the flush
  // itself emits no VCD command and leaves dumping enabled (continues as
  // before).
  auto content = ReadVcd();
  EXPECT_NE(content.find("b10100101 \""), std::string::npos);
  EXPECT_EQ(content.find("$dumpportsflush"), std::string::npos);
  EXPECT_TRUE(vcd.IsEnabled());
}

// §21.7.3.5 edge: with no dump file open the $dumpportsflush task is a harmless
// no-op. The dispatch guards on an active VCD writer, so issuing the task with
// no writer set neither flushes nor faults.
TEST_F(DumpportsflushSysTask, WithoutDumpFileIsHarmless) {
  SimFixture f;
  MakeVar(f, "data", 8, 0xA5);
  EvalExpr(MkSysCall(f.arena, "$dumpportsflush", {}), f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
}

}  // namespace
}  // namespace delta
