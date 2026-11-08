#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;

enum class UnpackedKind : std::uint8_t {
  kFixed,
  kDynamic,
  kQueue,
  kAssociative
};

UnpackedKind UnpackedDimKind(const Expr* dim, const TypeShapeTables& tables);

std::optional<DataType> IndexDimType(const Expr* dim);

struct UnpackedArrayType {
  DataType element;
  std::vector<Expr*> dims;
};

UnpackedArrayType WithTypedefDims(const DataType& element,
                                  std::vector<Expr*> dims,
                                  const TypeShapeTables& tables);

using TypeMatcher =
    std::function<std::optional<bool>(const DataType&, const DataType&)>;

std::optional<bool> UnpackedArrayTypesMatch(const UnpackedArrayType& a,
                                            const UnpackedArrayType& b,
                                            const TypeShapeTables& tables,
                                            const ScopeMap& constants,
                                            const TypeMatcher& match);

}  // namespace delta
