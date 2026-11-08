#pragma once

#include <string_view>

#include "preprocessor/protect_keywords.h"

using namespace delta;

inline ProtectKey KeyOf(std::string_view owner, std::string_view name,
                        std::string_view key) {
  ProtectKey held;
  held.owner = owner;
  held.name = name;
  held.key = key;
  return held;
}
