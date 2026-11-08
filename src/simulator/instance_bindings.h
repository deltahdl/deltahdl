#pragma once

#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;

struct InstanceBindings {
  std::vector<std::pair<const Expr*, Logic4Vec>> values;

  const Logic4Vec* Find(const Expr* site) const {
    for (const auto& [bound, value] : values) {
      if (bound == site) return &value;
    }
    return nullptr;
  }
};

}  // namespace delta
