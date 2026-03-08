#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, PolymorphicVTableMultiLevel) {
  SimFixture f;
  auto* base = MakeClassType(f, "A", {});
  auto* mid = MakeClassType(f, "B", {});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "C", {});
  leaf->parent = mid;

  auto* m_base = f.arena.Create<ModuleItem>();
  m_base->kind = ModuleItemKind::kFunctionDecl;
  m_base->name = "f";
  auto* m_leaf = f.arena.Create<ModuleItem>();
  m_leaf->kind = ModuleItemKind::kFunctionDecl;
  m_leaf->name = "f";

  base->vtable.push_back({"f", m_base, base});
  mid->vtable.push_back({"f", m_base, base});
  leaf->vtable.push_back({"f", m_leaf, leaf});

  auto [handle, obj] = MakeObj(f, leaf);
  EXPECT_EQ(obj->ResolveVirtualMethod("f"), m_leaf);
}

TEST(ClassSim, PolymorphicDispatchSubclassMethod) {
  SimFixture f;
  auto* base_type = MakeClassType(f, "BasePacket", {});
  auto* ether_type = MakeClassType(f, "EtherPacket", {});
  ether_type->parent = base_type;

  auto* base_send = f.arena.Create<ModuleItem>();
  base_send->kind = ModuleItemKind::kFunctionDecl;
  base_send->name = "send";
  auto* ether_send = f.arena.Create<ModuleItem>();
  ether_send->kind = ModuleItemKind::kFunctionDecl;
  ether_send->name = "send";

  base_type->vtable.push_back({"send", base_send, base_type});
  ether_type->vtable.push_back({"send", ether_send, ether_type});

  auto [handle, obj] = MakeObj(f, ether_type);
  EXPECT_EQ(obj->ResolveVirtualMethod("send"), ether_send);
}

TEST(ClassSim, NonVirtualFallbackToStaticResolution) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {});

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "bar";
  type->methods["bar"] = method;

  auto [handle, obj] = MakeObj(f, type);

  EXPECT_EQ(obj->ResolveVirtualMethod("bar"), nullptr);

  EXPECT_EQ(obj->ResolveMethod("bar"), method);
}

TEST(ClassSim, PolymorphicMiddleInheritsBase) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* mid = MakeClassType(f, "Mid", {});
  mid->parent = base;

  auto* base_fn = f.arena.Create<ModuleItem>();
  base_fn->kind = ModuleItemKind::kFunctionDecl;
  base_fn->name = "compute";

  base->vtable.push_back({"compute", base_fn, base});

  mid->vtable.push_back({"compute", base_fn, base});

  auto [handle, obj] = MakeObj(f, mid);
  EXPECT_EQ(obj->ResolveVirtualMethod("compute"), base_fn);
}

TEST(ClassSim, PolymorphicMultipleMethods) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});

  auto* send_fn = f.arena.Create<ModuleItem>();
  send_fn->kind = ModuleItemKind::kFunctionDecl;
  send_fn->name = "send";
  auto* recv_fn = f.arena.Create<ModuleItem>();
  recv_fn->kind = ModuleItemKind::kFunctionDecl;
  recv_fn->name = "receive";

  base->vtable.push_back({"send", send_fn, base});
  base->vtable.push_back({"receive", recv_fn, base});

  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;
  auto* derived_send = f.arena.Create<ModuleItem>();
  derived_send->kind = ModuleItemKind::kFunctionDecl;
  derived_send->name = "send";

  derived->vtable.push_back({"send", derived_send, derived});
  derived->vtable.push_back({"receive", recv_fn, base});

  auto [handle, obj] = MakeObj(f, derived);
  EXPECT_EQ(obj->ResolveVirtualMethod("send"), derived_send);
  EXPECT_EQ(obj->ResolveVirtualMethod("receive"), recv_fn);
}

TEST(ClassSim, PolymorphicUnknownMethodReturnsNull) {
  SimFixture f;
  auto* type = MakeClassType(f, "Foo", {});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_EQ(obj->ResolveVirtualMethod("nonexistent"), nullptr);
  EXPECT_EQ(obj->ResolveMethod("nonexistent"), nullptr);
}

}
