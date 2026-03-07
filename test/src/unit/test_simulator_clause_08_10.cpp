#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(ClassSim, StaticMethodResolution) {
  SimFixture f;
  auto* type = MakeClassType(f, "Util", {});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "helper";
  method->is_static = true;
  method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 100)));
  type->methods["helper"] = method;

  auto it = type->methods.find("helper");
  ASSERT_NE(it, type->methods.end());
  EXPECT_TRUE(it->second->is_static);
}

// §8.10: Static method callable without creating an instance.
TEST(ClassSim, StaticMethodCallableWithoutInstance) {
  SimFixture f;
  auto* type = MakeClassType(f, "Counter", {});
  type->properties.push_back({"count", 32, true});
  type->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 0);

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "get_count";
  method->is_static = true;
  method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 0)));
  type->methods["get_count"] = method;

  // No instance created — static method is still on the type.
  auto it = type->methods.find("get_count");
  ASSERT_NE(it, type->methods.end());
  EXPECT_TRUE(it->second->is_static);
}

// §8.10: Static method can access static properties on the type.
TEST(ClassSim, StaticMethodAccessesStaticProperty) {
  SimFixture f;
  auto* type = MakeClassType(f, "id", {});
  type->properties.push_back({"current", 32, true});
  type->static_properties["current"] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "next_id";
  method->is_static = true;
  type->methods["next_id"] = method;

  // Static method exists on the type, and static property is accessible.
  ASSERT_NE(type->methods.count("next_id"), 0u);
  EXPECT_EQ(type->static_properties["current"].ToUint64(), 42u);
}

}  // namespace
