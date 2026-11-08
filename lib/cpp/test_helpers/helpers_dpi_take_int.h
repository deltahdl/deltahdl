#pragma once

#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

inline DpiArgValue CallTakeIntReportingFormal(DpiRuntime& rt,
                                              const DpiArgValue& actual) {
  DpiRtFunction func;
  func.c_name = "c_take_int";
  func.sv_name = "take_int";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    return DpiArgValue::FromInt(a[0].type == DataTypeKind::kInt ? a[0].AsInt()
                                                                : -1);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {actual};
  return rt.CallImportWithArgs("take_int", actuals);
}
