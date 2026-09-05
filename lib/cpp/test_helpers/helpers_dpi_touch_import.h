#pragma once

#include <cstdint>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Registers the "touch" imported function into `rt`: an int function of one
// int formal, written in `direction`, whose foreign body reports the value it
// was handed through `seen` and leaves `wrote` in the formal's place.
//
// What it is for is the call a design makes: EvalDpiCall in
// src/simulator/eval_function_dpi.cpp reaches an import through the DpiRuntime
// the run holds, so a case asking what a SystemVerilog call site does with an
// argument reaches the import that way rather than by calling the registry
// itself. `seen` and the formal's direction are what those cases vary;
// §35.5.1.2 decides which of the two values crosses the call in each direction,
// and §35.5.1.1 that the crossing costs no simulation time.
inline void RegisterTouchImport(DpiRuntime& rt, Direction direction,
                                uint64_t wrote, uint64_t* seen) {
  DpiRtFunction func;
  func.c_name = "c_touch";
  func.sv_name = "touch";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"a", DataTypeKind::kInt, direction}};
  func.arg_impl = [wrote, seen](std::vector<DpiArgValue>& args) {
    *seen = static_cast<uint64_t>(args[0].AsInt());
    args[0] = DpiArgValue::FromInt(static_cast<int32_t>(wrote));
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));
}
