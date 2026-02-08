#include "simulation/driver_update.h"

#include "common/arena.h"

namespace delta {

DriverUpdate* DriverUpdatePool::Acquire() {
  if (free_list_) {
    DriverUpdate* update = free_list_;
    free_list_ = update->next;
    --free_count_;
    update->next = nullptr;
    return update;
  }
  return arena_.Create<DriverUpdate>();
}

void DriverUpdatePool::Release(DriverUpdate* update) {
  update->value = Logic4Vec{};
  update->drive_strength_0 = Strength::kStrong;
  update->drive_strength_1 = Strength::kStrong;
  update->driver_index = 0;
  update->next = free_list_;
  free_list_ = update;
  ++free_count_;
}

}  // namespace delta
