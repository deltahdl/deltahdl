// §6.16: String data type

#include "common/arena.h"
#include "common/types.h"
#include "simulation/adv_sim.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string>

using namespace delta;

namespace {

// =============================================================================
// SvString
// =============================================================================
TEST(AdvSim, SvStringDefaultEmpty) {
  SvString s;
  EXPECT_EQ(s.Len(), 0u);
  EXPECT_EQ(s.Get(), "");
}

TEST(AdvSim, SvStringSetAndGet) {
  SvString s;
  s.Set("hello");
  EXPECT_EQ(s.Get(), "hello");
  EXPECT_EQ(s.Len(), 5u);
}

TEST(AdvSim, SvStringCompare) {
  SvString a;
  SvString b;
  a.Set("abc");
  b.Set("abc");
  EXPECT_TRUE(a == b);
  b.Set("xyz");
  EXPECT_FALSE(a == b);
}

} // namespace
