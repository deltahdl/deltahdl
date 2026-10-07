#include "simulator/adv_sim.h"

#include <cstdint>
#include <vector>

#include "common/types.h"

namespace delta {

bool TwoStateDetector::Is2State(const Logic4Vec& vec) {
  for (uint32_t i = 0; i < vec.nwords; ++i) {
    if (vec.words[i].bval != 0) {
      return false;
    }
  }
  return true;
}

void EventCoalescer::Add(uint32_t target_id, uint64_t value) {
  pending_[target_id] = value;
}

std::vector<CoalescedEntry> EventCoalescer::Drain() {
  std::vector<CoalescedEntry> result;
  result.reserve(pending_.size());
  for (auto& [id, val] : pending_) {
    result.push_back({id, val});
  }
  pending_.clear();
  return result;
}

}  // namespace delta
