#pragma once

#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/net_data_type.h"

namespace delta {

struct DataType;

bool IsSimpleBitVectorType(const DataType& dtype,
                           const TypeShapeTables& tables);

struct UnboundedParam {
  std::string_view name;
  const DataType* dtype;
  bool has_unpacked_dims;
  SourceLoc loc;
};

void ValidateUnboundedParamType(const UnboundedParam& param,
                                const TypeShapeTables& tables,
                                DiagEngine& diag);

}  // namespace delta
