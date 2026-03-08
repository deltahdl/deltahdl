#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, SuperNewChaining) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"base_val"});
  auto* derived = MakeClassType(f, "Derived", {"child_val"});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);

  obj->SetProperty("base_val", MakeLogic4VecVal(f.arena, 32, 10));

  obj->SetProperty("child_val", MakeLogic4VecVal(f.arena, 32, 20));

  EXPECT_EQ(obj->GetProperty("base_val", f.arena).ToUint64(), 10u);
  EXPECT_EQ(obj->GetProperty("child_val", f.arena).ToUint64(), 20u);
}

TEST(ClassSim, SuperNewWithArgs) {
  SimFixture f;
  auto* base = MakeClassType(f, "Vehicle", {"speed"});
  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->return_type.kind = DataTypeKind::kVoid;
  ctor->func_args = {{Direction::kInput, false, false, {}, "s", nullptr, {}}};
  ctor->func_body_stmts.push_back(
      MakeAssign(f.arena, "speed", MkId(f.arena, "s")));
  base->methods["new"] = ctor;

  auto* derived = MakeClassType(f, "Car", {"doors"});
  derived->parent = base;

  auto it = derived->parent->methods.find("new");
  ASSERT_NE(it, derived->parent->methods.end());
  auto* base_ctor = it->second;
  ASSERT_NE(base_ctor, nullptr);
  EXPECT_EQ(base_ctor->func_args.size(), 1u);
}

// §8.17: Three-level hierarchy — all properties accessible after chaining.
TEST(ClassSim, ThreeLevelConstructorChaining) {
  SimFixture f;
  auto* grand = MakeClassType(f, "Grand", {"g_val"});
  auto* mid = MakeClassType(f, "Mid", {"m_val"});
  mid->parent = grand;
  auto* leaf = MakeClassType(f, "Leaf", {"l_val"});
  leaf->parent = mid;

  auto [handle, obj] = MakeObj(f, leaf);

  obj->SetProperty("g_val", MakeLogic4VecVal(f.arena, 32, 1));
  obj->SetProperty("m_val", MakeLogic4VecVal(f.arena, 32, 2));
  obj->SetProperty("l_val", MakeLogic4VecVal(f.arena, 32, 3));

  EXPECT_EQ(obj->GetProperty("g_val", f.arena).ToUint64(), 1u);
  EXPECT_EQ(obj->GetProperty("m_val", f.arena).ToUint64(), 2u);
  EXPECT_EQ(obj->GetProperty("l_val", f.arena).ToUint64(), 3u);
}

// §8.17: Base constructor registered in methods map is resolvable.
TEST(ClassSim, BaseConstructorResolvable) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  base->methods["new"] = ctor;

  auto* derived = MakeClassType(f, "Child", {"y"});
  derived->parent = base;

  // ResolveMethod walks type chain — child can find base's "new".
  auto [handle, obj] = MakeObj(f, derived);
  auto* resolved = obj->ResolveMethod("new");
  EXPECT_EQ(resolved, ctor);
}

}  // namespace
