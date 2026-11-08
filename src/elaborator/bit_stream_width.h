#pragma once

#include <cstdint>
#include <optional>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"

namespace delta {

struct DataType;
struct Expr;

std::optional<uint32_t> FixedDimElementCount(const Expr* dim,
                                             const ScopeMap& scope);

uint32_t FixedUnpackedElementCount(const std::vector<Expr*>& dims);

uint32_t BitStreamTypeWidth(const DataType& type, const TypedefMap& typedefs);

}  // namespace delta
