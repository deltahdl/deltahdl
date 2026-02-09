#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

// =============================================================================
// Clocking signal direction
// =============================================================================

enum class ClockingDir : uint8_t {
  kInput,
  kOutput,
  kInout,
};

// =============================================================================
// ClockingSignal: a signal within a clocking block with optional skew
// =============================================================================

struct ClockingSignal {
  std::string_view signal_name;
  ClockingDir direction = ClockingDir::kInput;
  SimTime skew{0};
};

// =============================================================================
// ClockingBlock: a named clocking block with default skews
// =============================================================================

struct ClockingBlock {
  std::string_view name;
  std::string_view clock_signal;
  SimTime default_input_skew{0};
  SimTime default_output_skew{0};
  std::vector<ClockingSignal> signals;
};

// =============================================================================
// ClockingManager: registers clocking blocks and applies skew
// =============================================================================

class ClockingManager {
 public:
  void Register(ClockingBlock block);
  const ClockingBlock* Find(std::string_view name) const;
  SimTime GetInputSkew(std::string_view block_name,
                       std::string_view signal_name) const;
  SimTime GetOutputSkew(std::string_view block_name,
                        std::string_view signal_name) const;
  uint32_t Count() const { return static_cast<uint32_t>(blocks_.size()); }

 private:
  const ClockingSignal* FindSignal(const ClockingBlock& block,
                                   std::string_view signal_name) const;

  std::vector<ClockingBlock> blocks_;
  std::unordered_map<std::string_view, size_t> name_index_;
};

}  // namespace delta
