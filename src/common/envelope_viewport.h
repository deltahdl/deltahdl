#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

inline constexpr std::string_view kViewportReadAccess = "r";
inline constexpr std::string_view kViewportReadWriteAccess = "rw";

enum class ViewportAccess : uint8_t { kNone, kRead, kReadWrite };

inline ViewportAccess ViewportAccessOf(std::string_view access) {
  if (access == kViewportReadAccess) return ViewportAccess::kRead;
  if (access == kViewportReadWriteAccess) return ViewportAccess::kReadWrite;
  return ViewportAccess::kNone;
}

struct EnvelopeViewport {
  std::string object;
  std::string access;
  SourceLoc loc;
  uint32_t first_source = 0;
  uint32_t last_source = 0;
  uint32_t region_source = 0;
  uint32_t first_line = 0;
  uint32_t last_line = 0;
};

}  // namespace delta
