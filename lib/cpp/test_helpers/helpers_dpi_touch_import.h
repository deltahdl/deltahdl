#pragma once

#include <cstdint>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi.h"

using namespace delta;

// Registers the "touch" imported function into `dpi`: an int function of one
// int formal, written in `direction`, whose foreign body reports the value it
// was handed through `seen` and leaves `wrote` in the formal's place.
//
// It is registered into a DpiContext rather than a DpiRuntime because what it
// is for is the call a design makes: EvalDpiCall in
// src/simulator/eval_function.cpp reaches an import through the DpiContext the
// run holds, so a case asking what a SystemVerilog call site does with an
// argument has to reach the import the same way. `seen` and the formal's
// direction are what those cases vary; §35.5.1.2 decides which of the two
// values crosses the call in each direction, and §35.5.1.1 that the crossing
// costs no simulation time.
inline void RegisterTouchImport(DpiContext& dpi, Direction direction,
                                uint64_t wrote, uint64_t* seen) {
  DpiFunction func;
  func.c_name = "c_touch";
  func.sv_name = "touch";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"a", DataTypeKind::kInt, direction}};
  func.arg_impl = [wrote, seen](std::vector<Logic4Word>& args) -> Logic4Word {
    *seen = args[0].aval;
    args[0] = Logic4Word{wrote, 0};
    return Logic4Word{0, 0};
  };
  dpi.RegisterImport(func);
}
