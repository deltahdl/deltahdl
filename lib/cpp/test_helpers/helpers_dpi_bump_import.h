#pragma once

#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

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
