#pragma once

#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

// Registers the canonical "bump" imported function into `rt`: a void import
// with a single int inout argument whose foreign body increments the argument
// by one. Used to exercise the change-detecting import path (§35.5.1.1 /
// §35.6.2), where calling "bump" on an inout actual must report exactly one
// value change of +1.
inline void RegisterBumpImport(DpiRuntime& rt) {
  DpiRtFunction func;
  func.c_name = "c_bump";
  func.sv_name = "bump";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"io", DataTypeKind::kInt, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(a[0].AsInt() + 1);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));
}
