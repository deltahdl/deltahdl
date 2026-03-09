#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

  auto it = base->methods.find("delay");
  ASSERT_NE(it, base->methods.end());
  EXPECT_EQ(it->second, base_delay);
}

TEST(ClassSim, SuperPropertyAccessFromBase) {
  SimFixture f;
  auto* base = MakeClassType(f, "Packet", {"value"});
  auto* derived = MakeClassType(f, "LinkedPacket", {"value"});
  derived->parent = base;

  EXPECT_EQ(base->properties.size(), 1u);
  EXPECT_EQ(derived->properties.size(), 1u);
  EXPECT_EQ(base->properties[0].name, "value");
  EXPECT_EQ(derived->properties[0].name, "value");
}

TEST(ClassSim, SuperParentAccessible) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* mid = MakeClassType(f, "Mid", {"y"});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "Leaf", {"z"});
  leaf->parent = mid;

  EXPECT_EQ(leaf->parent, mid);
  EXPECT_EQ(leaf->parent->name, "Mid");

  EXPECT_EQ(leaf->parent->parent, base);
}

}  // namespace
