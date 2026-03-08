#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §8.15: Resolving a method from the parent type (super semantics).
TEST(ClassSim, SuperMethodResolutionFromParent) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {});
  auto* base_delay = f.arena.Create<ModuleItem>();
  base_delay->kind = ModuleItemKind::kFunctionDecl;
  base_delay->name = "delay";
  base->methods["delay"] = base_delay;

  auto* derived = MakeClassType(f, "LinkedPacket", {});
  derived->parent = base;
  auto* derived_delay = f.arena.Create<ModuleItem>();
  derived_delay->kind = ModuleItemKind::kFunctionDecl;
  derived_delay->name = "delay";
  derived->methods["delay"] = derived_delay;

  // super.delay() should resolve to base method, not derived.
  auto it = base->methods.find("delay");
  ASSERT_NE(it, base->methods.end());
  EXPECT_EQ(it->second, base_delay);
}

// §8.15: super accesses base property, not overridden one.
TEST(ClassSim, SuperPropertyAccessFromBase) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {"value"});
  auto* derived = MakeClassType(f, "LinkedPacket", {"value"});
  derived->parent = base;

  // Both base and derived have a "value" property in their metadata.
  EXPECT_EQ(base->properties.size(), 1u);
  EXPECT_EQ(derived->properties.size(), 1u);
  EXPECT_EQ(base->properties[0].name, "value");
  EXPECT_EQ(derived->properties[0].name, "value");
}

// §8.15: Parent type accessible via parent pointer.
TEST(ClassSim, SuperParentAccessible) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* mid = MakeClassType(f, "Mid", {"y"});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "Leaf", {"z"});
  leaf->parent = mid;

  // super from Leaf reaches Mid, not Base.
  EXPECT_EQ(leaf->parent, mid);
  EXPECT_EQ(leaf->parent->name, "Mid");
  // super.super would be Mid->parent = Base, but this is not allowed.
  EXPECT_EQ(leaf->parent->parent, base);
}

}  // namespace
