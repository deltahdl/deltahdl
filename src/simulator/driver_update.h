#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

class Arena;

// --- DriverUpdate: temporary storage for a driven net value ---
// Used during net resolution (IEEE 1800-2023 §28.7) to hold each
// driver's contribution before combining via the net's resolution
// function.  Pooled via DriverUpdatePool to avoid allocation churn.

struct DriverUpdate {
  Logic4Vec value{};
  Strength drive_strength_0 = Strength::kStrong;
  Strength drive_strength_1 = Strength::kStrong;
  uint32_t driver_index = 0;
  DriverUpdate* next = nullptr;
};

// --- DriverUpdatePool: free-list recycler for DriverUpdate objects ---

class DriverUpdatePool {
 public:
  explicit DriverUpdatePool(Arena& arena) : arena_(arena) {}

  /// Acquire a DriverUpdate: pop from free-list or allocate from arena.
  DriverUpdate* Acquire();

  /// Release a DriverUpdate back to the free-list for reuse.
  void Release(DriverUpdate* update);

  /// Number of updates currently in the free-list.
  size_t FreeCount() const { return free_count_; }

 private:
  Arena& arena_;
  DriverUpdate* free_list_ = nullptr;
  size_t free_count_ = 0;
};

}  // namespace delta
