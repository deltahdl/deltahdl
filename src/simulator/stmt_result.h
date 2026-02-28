#pragma once

#include <cstdint>

namespace delta {

enum class StmtResult : uint8_t {
  kDone,
  kSuspendDelay,
  kSuspendEvent,
  kBreak,
  kContinue,
  kReturn,
};

}  // namespace delta
