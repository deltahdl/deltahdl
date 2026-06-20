#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

class Arena;

struct DriverUpdate {
  Logic4Vec value{};
  Strength drive_strength_0 = Strength::kStrong;
  Strength drive_strength_1 = Strength::kStrong;
  uint32_t driver_index = 0;
  DriverUpdate* next = nullptr;
};

class DriverUpdatePool {
 public:
  explicit DriverUpdatePool(Arena& arena) : arena_(arena) {}

  DriverUpdate* Acquire();

  void Release(DriverUpdate* update);

  size_t FreeCount() const { return free_count_; }

 private:
  Arena& arena_;
  DriverUpdate* free_list_ = nullptr;
  size_t free_count_ = 0;
};

}  // namespace delta
