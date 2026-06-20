#pragma once

#include <cstdint>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

using namespace delta;

// Opens a VCD file on the writer and registers a single signal, leaving the
// writer set as the active dump target on the simulation context. Mirrors the
// header/register/end-definitions/attach prologue every dump-limit test shares.
inline void SetupVcdDump(SimFixture& f, VcdWriter& vcd, std::string_view name,
                         uint32_t width, Variable* var) {
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal(name, width, var);  // ident '!'
  vcd.EndDefinitions();
  f.ctx.SetVcdWriter(&vcd);
}

// Drives 40 timestamped value changes through the writer, the workload the
// size-limiting tests use to grow the file past (or stay below) a byte budget.
// The variable counts up so each step is a real value change to be dumped.
inline void DriveValueChanges(SimFixture& f, VcdWriter& vcd, Variable* var,
                              uint32_t width) {
  var->prev_value = MakeLogic4VecVal(f.arena, width, 0x00);
  for (uint64_t t = 1; t <= 40; ++t) {
    var->value = MakeLogic4VecVal(f.arena, width, t & 0xFF);
    vcd.WriteTimestamp(t * 10);
    vcd.DumpChangedValues(0);
    var->prev_value = var->value;
  }
}

// Issues a size-limiting dump task (e.g. $dumplimit / $dumpportslimit) with the
// given byte budget on the active writer, then drives the standard 40-step
// value change workload so the limit machinery is exercised end to end.
inline void ApplyLimitAndDrive(SimFixture& f, VcdWriter& vcd, Variable* var,
                               uint32_t width, std::string_view task,
                               uint64_t limit) {
  EvalExpr(MkSysCall(f.arena, task, {MkInt(f.arena, limit)}), f.ctx, f.arena);
  DriveValueChanges(f, vcd, var, width);
}
