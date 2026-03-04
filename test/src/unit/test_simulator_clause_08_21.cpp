#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

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

}  // namespace
