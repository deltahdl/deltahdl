#pragma once

#include <optional>
#include <string_view>

#include "elaborator/expression_self_type.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"

namespace delta {

std::optional<DataType> NetOrVariableType(const RtlirModule& mod,
                                          std::string_view declared);

std::optional<DeclaredValue> NetOrVariableValue(const RtlirModule& mod,
                                                std::string_view declared);

}  // namespace delta
