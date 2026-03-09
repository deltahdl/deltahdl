#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, AbstractClassFlag) {
  SimFixture f;
  auto* abstract_type = MakeClassType(f, "AbstractBase", {});
  abstract_type->is_abstract = true;

  EXPECT_TRUE(abstract_type->is_abstract);
}

TEST(ClassSim, PureVirtualMethodNullBody) {
  SimFixture f;
  auto* abstract_type = MakeClassType(f, "Shape", {});
  abstract_type->is_abstract = true;

  abstract_type->vtable.push_back({"area", nullptr, abstract_type});
  EXPECT_EQ(abstract_type->vtable[0].method, nullptr);

  auto* concrete = MakeClassType(f, "Circle", {"radius"});
  concrete->parent = abstract_type;
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "area";
  method->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 314)));
  concrete->vtable.push_back({"area", method, concrete});

  auto [handle, obj] = MakeObj(f, concrete);
  auto* resolved = obj->ResolveVirtualMethod("area");
  EXPECT_EQ(resolved, method);
}

TEST(ClassSim, MultiplePureVirtualsOverridden) {
  SimFixture f;
  auto* abstract_type = MakeClassType(f, "Base", {});
  abstract_type->is_abstract = true;
  abstract_type->vtable.push_back({"area", nullptr, abstract_type});
  abstract_type->vtable.push_back({"perimeter", nullptr, abstract_type});

  auto* concrete = MakeClassType(f, "Rect", {"w", "h"});
  concrete->parent = abstract_type;

  auto* area_fn = f.arena.Create<ModuleItem>();
  area_fn->kind = ModuleItemKind::kFunctionDecl;
  area_fn->name = "area";
  concrete->vtable.push_back({"area", area_fn, concrete});

  auto* perim_fn = f.arena.Create<ModuleItem>();
  perim_fn->kind = ModuleItemKind::kFunctionDecl;
  perim_fn->name = "perimeter";
  concrete->vtable.push_back({"perimeter", perim_fn, concrete});

  auto [handle, obj] = MakeObj(f, concrete);
  EXPECT_EQ(obj->ResolveVirtualMethod("area"), area_fn);
  EXPECT_EQ(obj->ResolveVirtualMethod("perimeter"), perim_fn);
}

TEST(ClassSim, AbstractExtendsAbstractVtable) {
  SimFixture f;
  auto* base = MakeClassType(f, "Shape", {});
  base->is_abstract = true;
  base->vtable.push_back({"area", nullptr, base});

  auto* mid = MakeClassType(f, "Shape2D", {});
  mid->is_abstract = true;
  mid->parent = base;
  mid->vtable.push_back({"area", nullptr, base});
  mid->vtable.push_back({"perimeter", nullptr, mid});

  EXPECT_EQ(mid->vtable[0].method, nullptr);
  EXPECT_EQ(mid->vtable[1].method, nullptr);
}

TEST(ClassSim, ConcreteClassNotAbstract) {
  SimFixture f;
  auto* type = MakeClassType(f, "ConcreteClass", {"x"});
  EXPECT_FALSE(type->is_abstract);
}

}  // namespace
