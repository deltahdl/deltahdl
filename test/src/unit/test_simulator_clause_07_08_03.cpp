#include <algorithm>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §7.8.3: Null index (handle 0) is a valid key for class-indexed assoc arrays.
TEST(AssocArray, ClassIndex_NullKeyValid) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 64);
  int64_t null_key = static_cast<int64_t>(kNullClassHandle);
  aa->int_data[null_key] = MakeLogic4VecVal(f.arena, 32, 99);
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data[null_key].ToUint64(), 99u);
}

// §7.8.3: Class handles as keys produce distinct entries.
TEST(AssocArray, ClassIndex_DistinctHandles) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"id"});
  auto [h1, _1] = MakeObj(f, type);
  auto [h2, _2] = MakeObj(f, type);

  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 64);
  auto k1 = static_cast<int64_t>(h1);
  auto k2 = static_cast<int64_t>(h2);
  aa->int_data[k1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[k2] = MakeLogic4VecVal(f.arena, 32, 20);

  EXPECT_EQ(aa->int_data.size(), 2u);
  EXPECT_EQ(aa->int_data[k1].ToUint64(), 10u);
  EXPECT_EQ(aa->int_data[k2].ToUint64(), 20u);
}

// §7.8.3: Null key and object key can coexist.
TEST(AssocArray, ClassIndex_NullAndObjectCoexist) {
  SimFixture f;
  auto* type = MakeClassType(f, "Bar", {"x"});
  auto [h1, _1] = MakeObj(f, type);

  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 64);
  int64_t null_key = static_cast<int64_t>(kNullClassHandle);
  auto obj_key = static_cast<int64_t>(h1);
  aa->int_data[null_key] = MakeLogic4VecVal(f.arena, 32, 100);
  aa->int_data[obj_key] = MakeLogic4VecVal(f.arena, 32, 200);

  EXPECT_EQ(aa->int_data.size(), 2u);
  EXPECT_EQ(aa->int_data[null_key].ToUint64(), 100u);
  EXPECT_EQ(aa->int_data[obj_key].ToUint64(), 200u);
}

// §7.8.3: Overwriting an entry with the same class handle key.
TEST(AssocArray, ClassIndex_OverwriteEntry) {
  SimFixture f;
  auto* type = MakeClassType(f, "Key", {"v"});
  auto [h1, _1] = MakeObj(f, type);

  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 64);
  auto k1 = static_cast<int64_t>(h1);
  aa->int_data[k1] = MakeLogic4VecVal(f.arena, 32, 10);
  EXPECT_EQ(aa->int_data[k1].ToUint64(), 10u);

  aa->int_data[k1] = MakeLogic4VecVal(f.arena, 32, 42);
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data[k1].ToUint64(), 42u);
}

// §7.8.3: Ordering is deterministic (std::map provides sorted order by handle).
TEST(AssocArray, ClassIndex_DeterministicOrdering) {
  SimFixture f;
  auto* type = MakeClassType(f, "Item", {"id"});
  auto [h1, _1] = MakeObj(f, type);
  auto [h2, _2] = MakeObj(f, type);
  auto [h3, _3] = MakeObj(f, type);

  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 64);
  // Insert in non-sorted order.
  auto k2 = static_cast<int64_t>(h2);
  auto k3 = static_cast<int64_t>(h3);
  auto k1 = static_cast<int64_t>(h1);
  aa->int_data[k2] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->int_data[k3] = MakeLogic4VecVal(f.arena, 32, 3);
  aa->int_data[k1] = MakeLogic4VecVal(f.arena, 32, 1);

  // Iteration order is deterministic (sorted by key).
  std::vector<int64_t> keys;
  for (auto& [k, _] : aa->int_data) {
    keys.push_back(k);
  }
  EXPECT_EQ(keys.size(), 3u);
  // std::map guarantees sorted order — verify it's consistent.
  EXPECT_TRUE(std::is_sorted(keys.begin(), keys.end()));
}

// §7.8.3: Empty class-indexed assoc array has size 0.
TEST(AssocArray, ClassIndex_EmptySize) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 64);
  EXPECT_EQ(aa->Size(), 0u);
}

}  // namespace
