#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_buffered_dump.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises the $dumpflush system task end to end so the buffer-flushing
// semantics of §21.7.1.6 are observed as the production task path applies them.
class DumpflushSysTask : public VcdTestBase {};

// $dumpflush empties the dump file buffer so that all data written so far is
// stored in the file and is observable to a reader while the simulation is
// still running. Before the flush the records sit in the stream buffer and are
// not yet in the file; after the production $dumpflush path runs they are.
TEST_F(DumpflushSysTask, PushesBufferedOutputToFile) {
  SimFixture f;
  VcdWriter vcd(tmp_path_);
  SetupBufferedVcdDump(f, vcd, ReadVcd());

  EvalExpr(MkSysCall(f.arena, "$dumpflush", {}), f.ctx, f.arena);

  // After the flush the file reflects everything dumped so far.
  EXPECT_NE(ReadVcd().find("b10100101 \""), std::string::npos);
}

// After $dumpflush, dumping resumes exactly as before: the dump remains
// enabled, no value changes are lost, and the flush itself emits no VCD command
// (it is not a declaration or simulation command in the dump file).
TEST_F(DumpflushSysTask, ResumesDumpingWithoutLoss) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0x3C);
  data->prev_value = MakeLogic4VecVal(f.arena, 8, 0x00);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("data", 8, data);  // ident '!'
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    f.ctx.SetVcdWriter(&vcd);

    EvalExpr(MkSysCall(f.arena, "$dumpflush", {}), f.ctx, f.arena);
    EXPECT_TRUE(vcd.IsEnabled());  // dump state untouched by the flush

    // A change occurring after the flush is still recorded normally.
    vcd.WriteTimestamp(100);
    vcd.DumpChangedValues(0);
  }
  auto content = ReadVcd();
  // §21.7.2.2: shortest right-justified form drops 8'h3C's leading zeros.
  EXPECT_NE(content.find("b111100 !"), std::string::npos);  // change recorded
  EXPECT_EQ(content.find("$dumpflush"),
            std::string::npos);  // no command emitted
}

// "Resumed as before" holds symmetrically: when dumping is suspended at the
// time of the flush, $dumpflush still empties the buffer into the file (the
// flush is not gated by the enabled state) yet leaves the dump suspended so it
// continues exactly as it was.
TEST_F(DumpflushSysTask, FlushWhileSuspendedLeavesDumpSuspended) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0xA5);
  VcdWriter vcd(tmp_path_);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("data", 8, data);  // ident '!'
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  vcd.DumpAllValues();  // buffered while still enabled
  vcd.SetEnabled(false);

  f.ctx.SetVcdWriter(&vcd);
  EvalExpr(MkSysCall(f.arena, "$dumpflush", {}), f.ctx, f.arena);

  // The buffered records reached the file despite dumping being suspended...
  EXPECT_NE(ReadVcd().find("b10100101 !"), std::string::npos);
  // ...and the suspended state is preserved across the flush.
  EXPECT_FALSE(vcd.IsEnabled());
}

// With no dump file open the $dumpflush task is a harmless no-op.
TEST_F(DumpflushSysTask, WithoutDumpFileIsHarmless) {
  SimFixture f;
  MakeVar(f, "clk", 1, 1);
  EvalExpr(MkSysCall(f.arena, "$dumpflush", {}), f.ctx, f.arena);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
}

}  // namespace
}  // namespace delta
