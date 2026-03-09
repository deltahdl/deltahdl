#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, ExternMethodRegisteredSeparately) {
  SimFixture f;
  auto* type = MakeClassType(f, "MyClass", {"val"});

  auto* extern_method = f.arena.Create<ModuleItem>();
  extern_method->kind = ModuleItemKind::kFunctionDecl;
  extern_method->name = "get_val";
  extern_method->func_body_stmts.push_back(
      MakeReturn(f.arena, MkId(f.arena, "val")));

  type->methods["get_val"] = extern_method;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("get_val");
  EXPECT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->name, "get_val");
}

TEST(ClassSim, OutOfBlockBodyReplacesPrototype) {
  SimFixture f;
  auto* type = MakeClassType(f, "Packet", {});

  auto* proto = f.arena.Create<ModuleItem>();
  proto->kind = ModuleItemKind::kFunctionDecl;
  proto->name = "send";
  proto->is_extern = true;
  type->methods["send"] = proto;

  auto* body = f.arena.Create<ModuleItem>();
  body->kind = ModuleItemKind::kFunctionDecl;
  body->name = "send";
  body->method_class = "Packet";
  body->func_body_stmts.push_back(MakeReturn(f.arena, MkInt(f.arena, 100)));

  type->methods["send"] = body;

  auto* resolved = type->methods["send"];
  EXPECT_EQ(resolved, body);
  EXPECT_FALSE(resolved->func_body_stmts.empty());
}

TEST(ClassSim, OutOfBlockMethodResolvedViaResolveMethod) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {"x"});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "foo";
  method->method_class = "C";
  type->methods["foo"] = method;

  auto [handle, obj] = MakeObj(f, type);
  auto* resolved = obj->ResolveMethod("foo");
  EXPECT_EQ(resolved, method);
}

TEST(ClassSim, OutOfBlockConstructor) {
  SimFixture f;
  auto* type = MakeClassType(f, "C", {});

  auto* ctor = f.arena.Create<ModuleItem>();
  ctor->kind = ModuleItemKind::kFunctionDecl;
  ctor->name = "new";
  ctor->method_class = "C";
  type->methods["new"] = ctor;

  auto it = type->methods.find("new");
  ASSERT_NE(it, type->methods.end());
  EXPECT_EQ(it->second->method_class, "C");
}

}  // namespace
