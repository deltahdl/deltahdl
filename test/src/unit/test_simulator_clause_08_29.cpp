#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.29: Objects are dynamically allocated via AllocateClassObject.
TEST(ClassSim, MemMgmtDynamicAllocation) {
  SimFixture f;
  auto* type = MakeClassType(f, "MyClass", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_GT(handle, 0u);
  EXPECT_NE(obj, nullptr);
  EXPECT_EQ(f.ctx.GetClassObject(handle), obj);
}

// §8.29: Multiple objects allocated get unique handles.
TEST(ClassSim, MemMgmtUniqueHandles) {
  SimFixture f;
  auto* type = MakeClassType(f, "Obj", {"val"});
  auto [h1, o1] = MakeObj(f, type);
  auto [h2, o2] = MakeObj(f, type);
  EXPECT_NE(h1, h2);
  EXPECT_NE(o1, o2);
}

// §8.29: Null handle (0) returns nullptr.
TEST(ClassSim, MemMgmtNullHandle) {
  SimFixture f;
  EXPECT_EQ(f.ctx.GetClassObject(0), nullptr);
}

// §8.29: Object properties persist after allocation.
TEST(ClassSim, MemMgmtPropertiesPersist) {
  SimFixture f;
  auto* type = MakeClassType(f, "Persistent", {"data"});
  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("data", MakeLogic4VecVal(f.arena, 32, 42));
  auto* retrieved = f.ctx.GetClassObject(handle);
  ASSERT_NE(retrieved, nullptr);
  EXPECT_EQ(retrieved->GetProperty("data", f.arena).ToUint64(), 42u);
}

}  // namespace
