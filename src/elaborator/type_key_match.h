#pragma once

#include <string_view>

#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

bool IsTypeKey(std::string_view key, const TypedefMap& typedefs);

bool TypeKeyMatchesType(std::string_view key, const DataType& type,
                        const TypedefMap& typedefs);

bool TypeKeyMatchesMember(std::string_view key, const StructMember& member,
                          const TypedefMap& typedefs);

}  // namespace delta
