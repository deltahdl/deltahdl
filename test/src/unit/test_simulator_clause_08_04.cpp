// §8.4: Objects (class instance)

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Test fixture — provides arena, scheduler, sim context, and helpers to
// build class types and objects at the AST/runtime level.
// =============================================================================
struct ClassFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};
// Build a simple ClassTypeInfo and register it with the context.
static ClassTypeInfo *MakeClassType(
    ClassFixture &f, std::string_view name,
    const std::vector<std::string_view> &props) {
  auto *info = f.arena.Create<ClassTypeInfo>();
  info->name = name;
  for (auto p : props) {
    info->properties.push_back({p, 32, false});
  }
  f.ctx.RegisterClassType(name, info);
  return info;
}

// Allocate a ClassObject of the given type, returning (handle_id, object*).
static std::pair<uint64_t, ClassObject *> MakeObj(ClassFixture &f,
                                                  ClassTypeInfo *type) {
  auto *obj = f.arena.Create<ClassObject>();
  obj->type = type;
  // Initialize properties to 0.
  for (const auto &p : type->properties) {
    obj->properties[std::string(p.name)] =
        MakeLogic4VecVal(f.arena, p.width, 0);
  }
  uint64_t handle = f.ctx.AllocateClassObject(obj);
  return {handle, obj};
}

namespace {

// =============================================================================
// §8.6-8.8: Class declaration and new() constructor
// =============================================================================
TEST(ClassSim, AllocateNewObject) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Packet", {"header", "payload"});
  auto [handle, obj] = MakeObj(f, type);

  EXPECT_NE(handle, kNullClassHandle);
  EXPECT_EQ(obj->type, type);
  EXPECT_EQ(obj->GetProperty("header", f.arena).ToUint64(), 0u);
}

TEST(ClassSim, NewReturnsUniqueHandles) {
  ClassFixture f;
  auto *type = MakeClassType(f, "MyClass", {"x"});
  auto [h1, _1] = MakeObj(f, type);
  auto [h2, _2] = MakeObj(f, type);

  EXPECT_NE(h1, h2);
}

TEST(ClassSim, HandleToObjectLookup) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Foo", {"val"});
  auto [handle, obj] = MakeObj(f, type);

  auto *retrieved = f.ctx.GetClassObject(handle);
  EXPECT_EQ(retrieved, obj);
}

// =============================================================================
// §8.4: Null object handle checks
// =============================================================================
TEST(ClassSim, NullHandleIsZero) { EXPECT_EQ(kNullClassHandle, 0u); }

TEST(ClassSim, GetClassObjectNullReturnsNullptr) {
  ClassFixture f;
  auto *obj = f.ctx.GetClassObject(kNullClassHandle);
  EXPECT_EQ(obj, nullptr);
}

TEST(ClassSim, GetClassObjectInvalidReturnsNullptr) {
  ClassFixture f;
  auto *obj = f.ctx.GetClassObject(99999);
  EXPECT_EQ(obj, nullptr);
}

TEST(ClassSim, ClassTypeRegistryLookup) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Registry", {"x"});

  auto *found = f.ctx.FindClassType("Registry");
  EXPECT_EQ(found, type);

  auto *notfound = f.ctx.FindClassType("Nonexistent");
  EXPECT_EQ(notfound, nullptr);
}

TEST(ClassSim, MultipleObjectsSameType) {
  ClassFixture f;
  auto *type = MakeClassType(f, "Widget", {"value"});

  auto [h1, o1] = MakeObj(f, type);
  auto [h2, o2] = MakeObj(f, type);

  o1->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 100));
  o2->SetProperty("value", MakeLogic4VecVal(f.arena, 32, 200));

  // Each instance has independent properties.
  EXPECT_EQ(o1->GetProperty("value", f.arena).ToUint64(), 100u);
  EXPECT_EQ(o2->GetProperty("value", f.arena).ToUint64(), 200u);
}

}  // namespace
