#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_dumplimit.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Drives the $dumpportslimit system task end to end so the extended-VCD
// size-limiting semantics of §21.7.3.4 are observed as the production task path
// applies them. The byte budget is enforced by the 4-state size-limit machinery
// the extended VCD file inherits (§21.7.1.5).
class DumpportslimitSysTask : public VcdTestBase {};

// §21.7.3.4 C2/C3/C4: the leading filesize argument bounds the dump in bytes.
// The optional trailing filename names a $dumpports output but is dispatched
// the same way by this single-file writer, so with or without it the limit
// covers the one dump: once the file grows past the budget the dumper stops and
// a comment marking the limit is inserted, while value changes written below
// the limit are retained.
TEST_F(DumpportslimitSysTask, LimitStopsPortDumpAndInsertsComment) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0x00);
  {
    VcdWriter vcd(tmp_path_);
    SetupVcdDump(f, vcd, "data", 8, data);
    // Apply a modest byte budget through the production $dumpportslimit path;
    // the header fits but repeated value changes will eventually overrun it.
    ApplyLimitAndDrive(f, vcd, data, 8, "$dumpportslimit", 200);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("#10\n"), std::string::npos);  // early dump retained
  EXPECT_NE(content.find("$comment"),
            std::string::npos);                          // limit comment added
  EXPECT_EQ(content.find("#400\n"), std::string::npos);  // late dumps stopped
}

// §21.7.3.4 C2 negative control: the filesize argument value is honored, not a
// constant. With a budget far larger than the dump the limit is never reached,
// so every value change is recorded and no limit comment appears. Paired with
// the limit-reached test this shows the filesize the task is given controls the
// outcome.
TEST_F(DumpportslimitSysTask, DumpingContinuesBelowLimit) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0x00);
  {
    VcdWriter vcd(tmp_path_);
    SetupVcdDump(f, vcd, "data", 8, data);
    // A generous byte budget the dump never approaches.
    ApplyLimitAndDrive(f, vcd, data, 8, "$dumpportslimit", 1000000);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("#10\n"), std::string::npos);  // early dump present
  EXPECT_NE(content.find("#400\n"),
            std::string::npos);  // late dump still present
  EXPECT_EQ(content.find("$comment"), std::string::npos);  // no limit comment
}

// §21.7.3.4 edge: with no dump file open the $dumpportslimit task is a harmless
// no-op. The dispatch guards on an active VCD writer, so issuing the task with
// no writer set neither sets a limit nor faults.
TEST_F(DumpportslimitSysTask, WithoutDumpFileIsHarmless) {
  SimFixture f;
  MakeVar(f, "data", 8, 0x00);
  EvalExpr(MkSysCall(f.arena, "$dumpportslimit", {MkInt(f.arena, 200)}), f.ctx,
           f.arena);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
}

}  // namespace
}  // namespace delta
