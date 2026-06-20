#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.3.7 lifetimes of objects: vpiAutomatic is the Boolean lifetime selector
// (false => static, true => non-static), and vpiAllocScheme is the three-valued
// enumeration naming how an object's storage was obtained. These tests observe
// the production VpiObject state through vpi_get and the VpiAllocSchemeFor
// classification helper.

// L8 (static default) + L14 (vpiOtherScheme is the mandated default): a freshly
// constructed object is static and reports the Other allocation scheme.
TEST(ObjectLifetimes, DefaultObjectIsStaticWithOtherScheme) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject obj;
  EXPECT_EQ(vpi_get(vpiAutomatic, &obj), 0);
  EXPECT_EQ(vpi_get(vpiAllocScheme, &obj), vpiOtherScheme);
}

// L8 (true => non-static) + L12 (frame/thread => Automatic scheme): an object
// flagged automatic reports vpiAutomatic true and the Automatic scheme.
TEST(ObjectLifetimes, AutomaticObjectReportsAutomaticScheme) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject obj;
  obj.automatic = true;
  obj.alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kFrameOrThread);

  EXPECT_EQ(vpi_get(vpiAutomatic, &obj), 1);
  EXPECT_EQ(vpi_get(vpiAllocScheme, &obj), vpiAutomaticScheme);
}

// L13 (dynamic memory / class object => Dynamic scheme): an object allocated
// dynamically reports the Dynamic allocation scheme.
TEST(ObjectLifetimes, DynamicObjectReportsDynamicScheme) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject obj;
  obj.automatic = true;
  obj.alloc_scheme = VpiAllocSchemeFor(VpiAllocKind::kDynamic);

  EXPECT_EQ(vpi_get(vpiAllocScheme, &obj), vpiDynamicScheme);
}

// L11 (exactly three schemes) + L12/L13/L14: the classification helper maps
// each allocation category to its scheme, with Other as the fallthrough
// default.
TEST(ObjectLifetimes, AllocSchemeForCoversAllThreeKinds) {
  EXPECT_EQ(VpiAllocSchemeFor(VpiAllocKind::kFrameOrThread),
            vpiAutomaticScheme);
  EXPECT_EQ(VpiAllocSchemeFor(VpiAllocKind::kDynamic), vpiDynamicScheme);
  EXPECT_EQ(VpiAllocSchemeFor(VpiAllocKind::kOther), vpiOtherScheme);
}

// L9 + L10: vpiAutomatic is also a property of container objects (module,
// program, interface, package) and of a class definition / class typespec,
// where it expresses the default declared lifetime for variables of their
// tasks and functions. The production reports obj->automatic for any object
// type, so each container kind observes its own declared lifetime.
TEST(ObjectLifetimes, AutomaticIsAlsoAContainerAndClassProperty) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  const int kinds[] = {vpiModule, vpiProgram, vpiInterface, vpiPackage,
                       vpiClassTypespec};
  for (int kind : kinds) {
    VpiObject automatic_container;
    automatic_container.type = kind;
    automatic_container.automatic = true;
    EXPECT_EQ(vpi_get(vpiAutomatic, &automatic_container), 1)
        << "kind=" << kind;

    VpiObject static_container;
    static_container.type = kind;
    static_container.automatic = false;
    EXPECT_EQ(vpi_get(vpiAutomatic, &static_container), 0) << "kind=" << kind;
  }
}

}  // namespace
}  // namespace delta
