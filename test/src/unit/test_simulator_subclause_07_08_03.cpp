#include <algorithm>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassIndexAssocArraySimulation, ClassIndex_NullKeyValid) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, AssocArraySpec{64});
  auto null_key = static_cast<int64_t>(kNullClassHandle);
  aa->int_data[null_key] = MakeLogic4VecVal(f.arena, 32, 99);
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data[null_key].ToUint64(), 99u);
}

TEST(ClassIndexAssocArraySimulation, ClassIndex_DistinctHandles) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"id"});
  auto [h1, _1] = MakeObj(f, type);
  auto [h2, _2] = MakeObj(f, type);

  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, AssocArraySpec{64});
  auto k1 = static_cast<int64_t>(h1);
  auto k2 = static_cast<int64_t>(h2);
  aa->int_data[k1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[k2] = MakeLogic4VecVal(f.arena, 32, 20);

  EXPECT_EQ(aa->int_data.size(), 2u);
  EXPECT_EQ(aa->int_data[k1].ToUint64(), 10u);
  EXPECT_EQ(aa->int_data[k2].ToUint64(), 20u);
}

TEST(ClassIndexAssocArraySimulation, ClassIndex_NullAndObjectCoexist) {
  SimFixture f;
  auto* type = MakeClassType(f, "Bar", {"x"});
  auto [h1, _1] = MakeObj(f, type);

  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, AssocArraySpec{64});
  auto null_key = static_cast<int64_t>(kNullClassHandle);
  auto obj_key = static_cast<int64_t>(h1);
  aa->int_data[null_key] = MakeLogic4VecVal(f.arena, 32, 100);
  aa->int_data[obj_key] = MakeLogic4VecVal(f.arena, 32, 200);

  EXPECT_EQ(aa->int_data.size(), 2u);
  EXPECT_EQ(aa->int_data[null_key].ToUint64(), 100u);
  EXPECT_EQ(aa->int_data[obj_key].ToUint64(), 200u);
}

TEST(ClassIndexAssocArraySimulation, ClassIndex_OverwriteEntry) {
  SimFixture f;
  auto* type = MakeClassType(f, "Key", {"v"});
  auto [h1, _1] = MakeObj(f, type);

  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, AssocArraySpec{64});
  auto k1 = static_cast<int64_t>(h1);
  aa->int_data[k1] = MakeLogic4VecVal(f.arena, 32, 10);
  EXPECT_EQ(aa->int_data[k1].ToUint64(), 10u);

  aa->int_data[k1] = MakeLogic4VecVal(f.arena, 32, 42);
  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data[k1].ToUint64(), 42u);
}

TEST(ClassIndexAssocArraySimulation, ClassIndex_DeterministicOrdering) {
  SimFixture f;
  auto* type = MakeClassType(f, "Item", {"id"});
  auto [h1, _1] = MakeObj(f, type);
  auto [h2, _2] = MakeObj(f, type);
  auto [h3, _3] = MakeObj(f, type);

  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, AssocArraySpec{64});

  auto k2 = static_cast<int64_t>(h2);
  auto k3 = static_cast<int64_t>(h3);
  auto k1 = static_cast<int64_t>(h1);
  aa->int_data[k2] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->int_data[k3] = MakeLogic4VecVal(f.arena, 32, 3);
  aa->int_data[k1] = MakeLogic4VecVal(f.arena, 32, 1);

  std::vector<int64_t> keys;
  keys.reserve(aa->int_data.size());
  for (auto& [k, _] : aa->int_data) {
    keys.push_back(k);
  }
  EXPECT_EQ(keys.size(), 3u);

  EXPECT_TRUE(std::is_sorted(keys.begin(), keys.end()));
}

TEST(ClassIndexAssocArraySimulation, ClassIndex_EmptySize) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, AssocArraySpec{64});
  EXPECT_EQ(aa->Size(), 0u);
}

// §7.8.3 end to end: a class handle produced by §8.4 'new' is used as an index
// to store and then read back a value. Built from real source and run through
// the full pipeline so the runtime store/read is keyed by the handle the
// allocator actually produced, not by a hand-poked map entry.
TEST(ClassIndexAssocArraySimulation, EndToEndObjectHandleKeyWriteRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int result;\n"
      "  initial begin\n"
      "    Foo k;\n"
      "    k = new;\n"
      "    data[k] = 55;\n"
      "    result = data[k];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 55u);
}

// §7.8.3 end to end: two objects from separate §8.4 'new' calls are distinct
// keys, so a value stored under one handle does not disturb the other.
TEST(ClassIndexAssocArraySimulation, EndToEndDistinctObjectKeys) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int result;\n"
      "  initial begin\n"
      "    Foo a, b;\n"
      "    a = new;\n"
      "    b = new;\n"
      "    data[a] = 10;\n"
      "    data[b] = 20;\n"
      "    result = data[a];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 10u);
}

// §7.8.3 end to end: a null index is valid. Store and read back through the
// null handle key over the full lowering and evaluation path.
TEST(ClassIndexAssocArraySimulation, EndToEndNullKeyWriteRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "  int result;\n"
      "  initial begin\n"
      "    data[null] = 77;\n"
      "    result = data[null];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 77u);
}

// §7.8.3 end to end: a handle of a §8.13 derived class is a valid index into an
// array declared with the base class as index. The derived object built by
// 'new' keys the store, and the value reads back through the same handle.
TEST(ClassIndexAssocArraySimulation, EndToEndDerivedHandleKeyWriteRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class Base;\n"
      "    int id;\n"
      "  endclass\n"
      "  class Derived extends Base;\n"
      "    int extra;\n"
      "  endclass\n"
      "  int data[Base];\n"
      "  int result;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    data[d] = 88;\n"
      "    result = data[d];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 88u);
}

}  // namespace
