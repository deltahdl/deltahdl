#pragma once

#include <string_view>

#include "preprocessor/protect_keywords.h"

using namespace delta;

// One key an entity provided, held under the name that picks it out of that
// entity's list. Neither half reaches a key alone, so the two are supplied
// together the way §34.5.12 identifies a key.
inline ProtectKey KeyOf(std::string_view owner, std::string_view name,
                        std::string_view key) {
  ProtectKey held;
  held.owner = owner;
  held.name = name;
  held.key = key;
  return held;
}
