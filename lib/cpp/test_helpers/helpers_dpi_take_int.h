#pragma once

#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

// Registers a "take_int" DPI import on `rt` whose int formal reports back the
// value it observed (or -1 if the callee did not see a kInt formal), then calls
// it with the single `actual` and returns the callee's reported result. This is
// the shared §35.6.1 / §35.6.1.1 setup for the input-coercion and WYSIWYG
// declared-type tests, which differ only in the actual presented and the value
// expected back.
inline DpiArgValue CallTakeIntReportingFormal(DpiRuntime& rt,
                                              DpiArgValue actual) {
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
