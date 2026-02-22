// §non_lrm

#include "common/arena.h"
#include "common/types.h"
#include "simulation/driver_update.h"
#include <gtest/gtest.h>

using namespace delta;

namespace {

// --- DriverUpdate struct tests ---
TEST(DriverUpdate, DefaultConstruction_ValueFields) {
  DriverUpdate du;
  EXPECT_EQ(du.value.width, 0);
  EXPECT_EQ(du.value.nwords, 0);
  EXPECT_EQ(du.value.words, nullptr);
}

TEST(DriverUpdate, DefaultConstruction_StrengthAndIndex) {
  DriverUpdate du;
  EXPECT_EQ(du.drive_strength_0, Strength::kStrong);
  EXPECT_EQ(du.drive_strength_1, Strength::kStrong);
  EXPECT_EQ(du.driver_index, 0);
  EXPECT_EQ(du.next, nullptr);
}

// --- DriverUpdatePool tests ---
TEST(DriverUpdatePool, AcquireCreatesNew) {
  Arena arena;
  DriverUpdatePool pool(arena);
  DriverUpdate *du = pool.Acquire();
  ASSERT_NE(du, nullptr);
  EXPECT_EQ(du->value.width, 0);
  EXPECT_EQ(du->drive_strength_0, Strength::kStrong);
  EXPECT_EQ(du->drive_strength_1, Strength::kStrong);
}

TEST(DriverUpdatePool, AcquireCreatesNewDefaults) {
  Arena arena;
  DriverUpdatePool pool(arena);
  DriverUpdate *du = pool.Acquire();
  ASSERT_NE(du, nullptr);
  EXPECT_EQ(du->driver_index, 0);
  EXPECT_EQ(du->next, nullptr);
}

TEST(DriverUpdatePool, ReleaseAndReuse_SamePointer) {
  Arena arena;
  DriverUpdatePool pool(arena);
  DriverUpdate *du = pool.Acquire();

  // Modify all fields.
  du->value = MakeLogic4VecVal(arena, 8, 0xFF);
  du->drive_strength_0 = Strength::kWeak;
  du->drive_strength_1 = Strength::kPull;
  du->driver_index = 42;

  pool.Release(du);
  EXPECT_EQ(pool.FreeCount(), 1);

  DriverUpdate *reused = pool.Acquire();
  EXPECT_EQ(reused, du); // Same pointer returned.
  EXPECT_EQ(pool.FreeCount(), 0);
}

TEST(DriverUpdatePool, ReleaseAndReuse_FieldsReset) {
  Arena arena;
  DriverUpdatePool pool(arena);
  DriverUpdate *du = pool.Acquire();

  // Modify all fields.
  du->value = MakeLogic4VecVal(arena, 8, 0xFF);
  du->drive_strength_0 = Strength::kWeak;
  du->drive_strength_1 = Strength::kPull;
  du->driver_index = 42;

  pool.Release(du);
  DriverUpdate *reused = pool.Acquire();
  // All fields reset to defaults.
  EXPECT_EQ(reused->value.width, 0);
  EXPECT_EQ(reused->drive_strength_0, Strength::kStrong);
  EXPECT_EQ(reused->drive_strength_1, Strength::kStrong);
  EXPECT_EQ(reused->driver_index, 0);
  EXPECT_EQ(reused->next, nullptr);
}

TEST(DriverUpdatePool, FreeCount) {
  Arena arena;
  DriverUpdatePool pool(arena);
  EXPECT_EQ(pool.FreeCount(), 0);

  DriverUpdate *du1 = pool.Acquire();
  DriverUpdate *du2 = pool.Acquire();
  pool.Release(du1);
  pool.Release(du2);
  EXPECT_EQ(pool.FreeCount(), 2);

  pool.Acquire();
  EXPECT_EQ(pool.FreeCount(), 1);
}

TEST(DriverUpdatePool, MultipleAcquireReleaseCycles) {
  Arena arena;
  DriverUpdatePool pool(arena);

  // Acquire several, release all, acquire again.
  constexpr size_t kCount = 10;
  DriverUpdate *updates[kCount];
  for (size_t i = 0; i < kCount; ++i) {
    updates[i] = pool.Acquire();
    ASSERT_NE(updates[i], nullptr);
  }
  EXPECT_EQ(pool.FreeCount(), 0);

  for (size_t i = 0; i < kCount; ++i) {
    pool.Release(updates[i]);
  }
  EXPECT_EQ(pool.FreeCount(), kCount);

  // Re-acquire all — should reuse, no new arena allocation.
  size_t initial_alloc = arena.TotalAllocated();
  for (size_t i = 0; i < kCount; ++i) {
    pool.Acquire();
  }
  EXPECT_EQ(pool.FreeCount(), 0);
  EXPECT_EQ(arena.TotalAllocated(), initial_alloc);
}

TEST(DriverUpdatePool, AcquireAfterPartialRelease) {
  Arena arena;
  DriverUpdatePool pool(arena);

  DriverUpdate *du1 = pool.Acquire();
  DriverUpdate *du2 = pool.Acquire();
  DriverUpdate *du3 = pool.Acquire();

  // Release du2 only.
  pool.Release(du2);
  EXPECT_EQ(pool.FreeCount(), 1);

  // Next acquire should return du2.
  DriverUpdate *reused = pool.Acquire();
  EXPECT_EQ(reused, du2);
  EXPECT_EQ(pool.FreeCount(), 0);

  // Suppress unused-variable warnings.
  (void)du1;
  (void)du3;
}

} // namespace
