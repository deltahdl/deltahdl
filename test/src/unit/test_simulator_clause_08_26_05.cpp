#include "fixture_simulator.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.26.5: Interface class type — IsA works through implementing class.
TEST(ClassSim, InterfaceClassIsACheck) {
  SimFixture f;

  auto* iface_type = f.arena.Create<ClassTypeInfo>();
  iface_type->name = "IC";
  iface_type->is_interface = true;
  f.ctx.RegisterClassType("IC", iface_type);

  auto* impl_type = f.arena.Create<ClassTypeInfo>();
  impl_type->name = "C";
  impl_type->parent = iface_type;
  f.ctx.RegisterClassType("C", impl_type);

  // C IsA IC (through parent chain).
  EXPECT_TRUE(impl_type->IsA(iface_type));
  // IC is not IsA C.
  EXPECT_FALSE(iface_type->IsA(impl_type));
}

}  // namespace
