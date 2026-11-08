#pragma once

#include <cstdint>

namespace delta {

enum class VpiAllocKind : std::uint8_t {
  kFrameOrThread,
  kDynamic,
  kOther,
};

int VpiAllocSchemeFor(VpiAllocKind kind);

}  // namespace delta
