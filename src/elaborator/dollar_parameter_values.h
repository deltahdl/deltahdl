#pragma once

#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/net_data_type.h"

namespace delta {

struct CompilationUnit;
struct DataType;
struct Expr;

struct DollarParamValue {
  std::string_view name;
  const Expr* value;
  const DataType* type;
  bool has_unpacked_dims;
};

void CheckDollarParamValue(const DollarParamValue& param,
                           const TypeShapeTables& tables, DiagEngine& diag);

void CheckClassParamDollarValues(const CompilationUnit* unit,
                                 const TypeShapeTables& tables,
                                 DiagEngine& diag);

}  // namespace delta
