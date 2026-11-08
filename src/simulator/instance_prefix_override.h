#pragma once

#include <string>
#include <string_view>
#include <utility>

namespace delta {

struct InstancePrefixOverrideState {
  bool active = false;
  std::string prefix;
};

class InstancePrefixOverride {
 public:
  InstancePrefixOverride(InstancePrefixOverrideState& state,
                         std::string_view prefix)
      : state_(state), saved_(state) {
    state_.active = true;
    state_.prefix = std::string(prefix);
  }

  ~InstancePrefixOverride() { state_ = std::move(saved_); }

  InstancePrefixOverride(const InstancePrefixOverride&) = delete;
  InstancePrefixOverride& operator=(const InstancePrefixOverride&) = delete;

 private:
  InstancePrefixOverrideState& state_;
  InstancePrefixOverrideState saved_;
};

}  // namespace delta
