#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/adv_sim.h"

using namespace delta;

// =============================================================================
// TwoStateDetector
// =============================================================================

TEST(AdvSim, TwoStateDetectorKnown2State) {
  Arena arena;
  auto vec = MakeLogic4VecVal(arena, 8, 0x42);
  EXPECT_TRUE(TwoStateDetector::Is2State(vec));
}

TEST(AdvSim, TwoStateDetectorWith4StateValue) {
  Arena arena;
  auto vec = MakeLogic4Vec(arena, 8);
  // Set bval to non-zero to indicate X/Z.
  vec.words[0].bval = 0x01;
  EXPECT_FALSE(TwoStateDetector::Is2State(vec));
}

TEST(AdvSim, TwoStateDetectorZeroWidth) {
  Logic4Vec empty;
  empty.width = 0;
  empty.nwords = 0;
  empty.words = nullptr;
  EXPECT_TRUE(TwoStateDetector::Is2State(empty));
}

// =============================================================================
// EventCoalescer
// =============================================================================

TEST(AdvSim, EventCoalescerMergesDuplicates) {
  EventCoalescer coalescer;
  uint32_t target_id = 42;
  coalescer.Add(target_id, 100);
  coalescer.Add(target_id, 200);
  coalescer.Add(target_id, 300);
  // Only last value for each target should survive.
  auto entries = coalescer.Drain();
  ASSERT_EQ(entries.size(), 1u);
  EXPECT_EQ(entries[0].target_id, target_id);
  EXPECT_EQ(entries[0].value, 300u);
}

TEST(AdvSim, EventCoalescerKeepsDistinctTargets) {
  EventCoalescer coalescer;
  coalescer.Add(1, 10);
  coalescer.Add(2, 20);
  coalescer.Add(3, 30);
  auto entries = coalescer.Drain();
  EXPECT_EQ(entries.size(), 3u);
}

TEST(AdvSim, EventCoalescerDrainClearsState) {
  EventCoalescer coalescer;
  coalescer.Add(1, 10);
  auto first = coalescer.Drain();
  EXPECT_EQ(first.size(), 1u);
  auto second = coalescer.Drain();
  EXPECT_TRUE(second.empty());
}

// =============================================================================
// DynArray
// =============================================================================

TEST(AdvSim, DynArrayDefaultEmpty) {
  DynArray arr;
  EXPECT_EQ(arr.Size(), 0u);
}

TEST(AdvSim, DynArrayPushAndAccess) {
  DynArray arr;
  arr.Push(42);
  arr.Push(99);
  EXPECT_EQ(arr.Size(), 2u);
  EXPECT_EQ(arr.At(0), 42u);
  EXPECT_EQ(arr.At(1), 99u);
}

TEST(AdvSim, DynArrayDelete) {
  DynArray arr;
  arr.Push(10);
  arr.Push(20);
  arr.Delete();
  EXPECT_EQ(arr.Size(), 0u);
}

// =============================================================================
// AssocArray
// =============================================================================

TEST(AdvSim, AssocArrayInsertAndLookup) {
  AssocArray arr;
  arr.Insert("key1", 100);
  arr.Insert("key2", 200);
  EXPECT_EQ(arr.Size(), 2u);
  EXPECT_EQ(arr.Lookup("key1"), 100u);
  EXPECT_EQ(arr.Lookup("key2"), 200u);
}

TEST(AdvSim, AssocArrayExistsAndErase) {
  AssocArray arr;
  arr.Insert("k", 1);
  EXPECT_TRUE(arr.Exists("k"));
  EXPECT_FALSE(arr.Exists("other"));
  arr.Erase("k");
  EXPECT_FALSE(arr.Exists("k"));
  EXPECT_EQ(arr.Size(), 0u);
}

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
