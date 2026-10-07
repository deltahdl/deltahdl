#pragma once

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

class TwoStateDetector {
 public:
  static bool Is2State(const Logic4Vec& vec);
};

struct CoalescedEntry {
  uint32_t target_id;
  uint64_t value;
};

class EventCoalescer {
 public:
  void Add(uint32_t target_id, uint64_t value);
  std::vector<CoalescedEntry> Drain();

 private:
  std::unordered_map<uint32_t, uint64_t> pending_;
};

class SvString {
 public:
  uint32_t Len() const { return static_cast<uint32_t>(data_.size()); }
  const std::string& Get() const { return data_; }
  void Set(const std::string& val) { data_ = val; }
  bool operator==(const SvString& other) const { return data_ == other.data_; }

 private:
  std::string data_;
};

}  // namespace delta
