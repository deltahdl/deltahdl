#pragma once

#include <cstdint>

namespace delta {

enum class PropertyInstancePlacement : uint8_t {
  kAsPropertyExpr,
  kAsPropertySpec,
};

bool IsPropertyInstanceLegal(PropertyInstancePlacement placement,
                             bool body_substitutable_at_placement);

}  // namespace delta
