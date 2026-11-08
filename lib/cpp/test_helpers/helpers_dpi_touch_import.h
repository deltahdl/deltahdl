#pragma once

#include <cstdint>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

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
