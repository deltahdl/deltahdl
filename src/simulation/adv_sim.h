#pragma once

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

// =============================================================================
// 2-state fast path detector
// =============================================================================

class TwoStateDetector {
 public:
  static bool Is2State(const Logic4Vec& vec);
};

// =============================================================================
// Event coalescing
// =============================================================================

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

// =============================================================================
// Dynamic array (SV dynamic arrays)
// =============================================================================

class DynArray {
 public:
  uint32_t Size() const { return static_cast<uint32_t>(data_.size()); }
  void Push(uint64_t val);
  uint64_t At(uint32_t idx) const;
  void Delete();

 private:
  std::vector<uint64_t> data_;
};

// =============================================================================
// Associative array (SV associative arrays)
// =============================================================================

class AssocArray {
 public:
  uint32_t Size() const { return static_cast<uint32_t>(data_.size()); }
  void Insert(const std::string& key, uint64_t val);
  uint64_t Lookup(const std::string& key) const;
  bool Exists(const std::string& key) const;
  void Erase(const std::string& key);

 private:
  std::unordered_map<std::string, uint64_t> data_;
};

// =============================================================================
// SystemVerilog string type
// =============================================================================

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
