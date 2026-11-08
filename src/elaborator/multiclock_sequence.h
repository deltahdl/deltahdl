#ifndef DELTA_ELABORATOR_MULTICLOCK_SEQUENCE_H
#define DELTA_ELABORATOR_MULTICLOCK_SEQUENCE_H

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace delta {

enum class MulticlockJoin : std::uint8_t {
  kLeading,
  kSingleDelay,
  kZeroDelay,
  kOther,
};

struct MulticlockSubsequence {
  std::string clock;
  MulticlockJoin join = MulticlockJoin::kLeading;
  bool admits_empty = false;
};

std::optional<std::string> CheckMulticlockSequenceLegality(
    const std::vector<MulticlockSubsequence>& subsequences);

}  // namespace delta

#endif
