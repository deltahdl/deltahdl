#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

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
