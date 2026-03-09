#include "fixture_simulator.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

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

  EXPECT_TRUE(impl_type->IsA(iface_type));

  EXPECT_FALSE(iface_type->IsA(impl_type));
}

}  // namespace
