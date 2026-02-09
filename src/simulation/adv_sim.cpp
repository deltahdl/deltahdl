#include "simulation/adv_sim.h"

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace delta {

// =============================================================================
// TwoStateDetector
// =============================================================================

bool TwoStateDetector::Is2State(const Logic4Vec& vec) {
  for (uint32_t i = 0; i < vec.nwords; ++i) {
    if (vec.words[i].bval != 0) {
      return false;
    }
  }
  return true;
}

// =============================================================================
// EventCoalescer
// =============================================================================

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

// =============================================================================
// DynArray
// =============================================================================

void DynArray::Push(uint64_t val) { data_.push_back(val); }

uint64_t DynArray::At(uint32_t idx) const {
  if (idx >= data_.size()) return 0;
  return data_[idx];
}

void DynArray::Delete() { data_.clear(); }

// =============================================================================
// AssocArray
// =============================================================================

void AssocArray::Insert(const std::string& key, uint64_t val) {
  data_[key] = val;
}

uint64_t AssocArray::Lookup(const std::string& key) const {
  auto it = data_.find(key);
  if (it == data_.end()) return 0;
  return it->second;
}

bool AssocArray::Exists(const std::string& key) const {
  return data_.count(key) != 0;
}

void AssocArray::Erase(const std::string& key) { data_.erase(key); }

}  // namespace delta
