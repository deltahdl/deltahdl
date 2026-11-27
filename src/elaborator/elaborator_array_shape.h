#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;

DataTypeKind ElementKindThroughTypedefs(const DataType& dtype,
                                        const TypedefMap& typedefs);

std::string_view ElementTypeIdentity(const DataType& dtype,
                                     const TypedefMap& typedefs);

const DataType* ElementAggregate(const DataType& dtype,
                                 const TypedefMap& typedefs);

std::vector<std::optional<uint32_t>> ElementUnpackedShape(
    const DataType& dtype, const TypedefMap& typedefs,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        typedef_dims,
    const ScopeMap& scope);

std::vector<std::optional<uint32_t>> UnpackedShapeOf(
    const DataType& elem, const std::vector<Expr*>& dims,
    const std::unordered_set<std::string_view>& aggregate_typedefs,
    const ScopeMap& scope);

}  // namespace delta
