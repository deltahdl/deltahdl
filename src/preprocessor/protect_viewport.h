#pragma once

#include <string>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

inline constexpr std::string_view kViewportKeyword = "viewport";

inline constexpr std::string_view kObjectSubkeyword = "object";
inline constexpr std::string_view kAccessSubkeyword = "access";

struct ProtectViewport {
  std::string object;
  std::string access;
  bool stated = false;
  SourceLoc loc;
};

ProtectViewport ParseProtectViewport(std::string_view value);

}  // namespace delta
