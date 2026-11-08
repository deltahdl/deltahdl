#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

enum class AssertionControlTaskCategory : uint8_t {
  kAssertTask,
  kAssertActionTask,
  kAssertControl,
  kNotAssertionControlTask,
};

AssertionControlTaskCategory ClassifyAssertionControlTask(
    std::string_view name);

bool IsAssertionControlTaskName(std::string_view name);

}  // namespace delta
