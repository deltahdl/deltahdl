#pragma once

#include <cstdint>

namespace delta {

enum class ActionBlockStatementForm : uint8_t {
  kConcurrentAssert,
  kConcurrentAssume,
  kConcurrentCover,
  kImmediateAssertion,
  kOther,
};

bool ConcurrentAssertActionBlockAllows(ActionBlockStatementForm form);

}  // namespace delta
