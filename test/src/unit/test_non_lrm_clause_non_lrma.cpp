// §non_lrm

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

namespace {

TEST(Arena, Allocation) {
  Arena arena;
  const auto *p1 = arena.AllocArray<uint64_t>(10);
  ASSERT_NE(p1, nullptr);
  auto *p2 = arena.AllocArray<uint32_t>(100);
  ASSERT_NE(p2, nullptr);
  EXPECT_NE(p1, reinterpret_cast<const uint64_t *>(p2));
  EXPECT_GT(arena.TotalAllocated(), 0);
}

TEST(Arena, StringAllocation) {
  Arena arena;
  const char *src = "hello";
  auto *s = arena.AllocString(src, 5);
  EXPECT_EQ(std::string_view(s), "hello");
}

TEST(Arena, Reset) {
  Arena arena;
  arena.AllocArray<char>(1000);
  EXPECT_EQ(arena.TotalAllocated(), 1000);
  arena.Reset();
  EXPECT_EQ(arena.TotalAllocated(), 0);
}

}  // namespace
