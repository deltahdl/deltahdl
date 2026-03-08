#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, HandleAssignmentSharesObject) {
  SimFixture f;
  auto* type = MakeClassType(f, "Data", {"val"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 10));

  auto* retrieved = f.ctx.GetClassObject(handle);
  EXPECT_EQ(retrieved, obj);
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 10u);

  obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(retrieved->GetProperty("val", f.arena).ToUint64(), 20u);
}

TEST(ClassSim, HandleNullAssignment) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {"x"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_NE(f.ctx.GetClassObject(handle), nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(handle), obj);

  uint64_t null_handle = kNullClassHandle;
  EXPECT_EQ(f.ctx.GetClassObject(null_handle), nullptr);
}

// §8.12: Shallow copy creates a new independent object.
TEST(ClassSim, ShallowCopyCreatesNewObject) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {"data"});
  auto [h1, obj1] = MakeObj(f, type);
  obj1->SetProperty("data", MakeLogic4VecVal(f.arena, 32, 42));

  auto* copy = obj1->ShallowCopy(f.arena);
  ASSERT_NE(copy, nullptr);
  EXPECT_NE(copy, obj1);
  EXPECT_EQ(copy->type, obj1->type);
  EXPECT_EQ(copy->GetProperty("data", f.arena).ToUint64(), 42u);
}

// §8.12: Shallow copy properties are independent from original.
TEST(ClassSim, ShallowCopyPropertiesIndependent) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"x"});
  auto [h1, obj1] = MakeObj(f, type);
  obj1->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 10));

  auto* copy = obj1->ShallowCopy(f.arena);

  // Modifying copy doesn't affect original.
  copy->SetProperty("x", MakeLogic4VecVal(f.arena, 32, 99));
  EXPECT_EQ(obj1->GetProperty("x", f.arena).ToUint64(), 10u);
  EXPECT_EQ(copy->GetProperty("x", f.arena).ToUint64(), 99u);
}

// §8.12: Shallow copy preserves all properties.
TEST(ClassSim, ShallowCopyPreservesAllProperties) {
  SimFixture f;
  auto* type = MakeClassType(f, "Multi", {"a", "b", "c"});
  auto [h1, obj1] = MakeObj(f, type);
  obj1->SetProperty("a", MakeLogic4VecVal(f.arena, 32, 1));
  obj1->SetProperty("b", MakeLogic4VecVal(f.arena, 32, 2));
  obj1->SetProperty("c", MakeLogic4VecVal(f.arena, 32, 3));

  auto* copy = obj1->ShallowCopy(f.arena);
  EXPECT_EQ(copy->GetProperty("a", f.arena).ToUint64(), 1u);
  EXPECT_EQ(copy->GetProperty("b", f.arena).ToUint64(), 2u);
  EXPECT_EQ(copy->GetProperty("c", f.arena).ToUint64(), 3u);
}

// §8.12: Shallow copy of object containing a class handle copies handle only.
TEST(ClassSim, ShallowCopySharesNestedHandles) {
  SimFixture f;
  auto* inner_type = MakeClassType(f, "Inner", {"val"});
  auto [inner_handle, inner_obj] = MakeObj(f, inner_type);
  inner_obj->SetProperty("val", MakeLogic4VecVal(f.arena, 32, 77));

  auto* outer_type = MakeClassType(f, "Outer", {"ref"});
  auto [outer_handle, outer_obj] = MakeObj(f, outer_type);
  // Store inner handle as a property value.
  outer_obj->SetProperty("ref", MakeLogic4VecVal(f.arena, 64, inner_handle));

  auto* copy = outer_obj->ShallowCopy(f.arena);
  // The copy has the same handle value — both point to the same inner object.
  EXPECT_EQ(copy->GetProperty("ref", f.arena).ToUint64(), inner_handle);
}

}  // namespace
