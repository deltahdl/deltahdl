#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(InterfaceClassSimulation, InterfaceClassTypeInfoFlag) {
  SimFixture f;

  auto* decl = f.arena.Create<ClassDecl>();
  decl->name = "IC";
  decl->is_interface = true;

  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "IC";
  info->decl = decl;
  info->is_interface = true;
  info->is_abstract = false;
  f.ctx.RegisterClassType("IC", info);

  auto* found = f.ctx.FindClassType("IC");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_interface);
}

TEST(InterfaceClassSimulation, InterfaceClassVtableEntries) {
  SimFixture f;

  auto* decl = f.arena.Create<ClassDecl>();
  decl->name = "IC";
  decl->is_interface = true;

  auto* info = f.arena.Create<ClassTypeInfo>();
  info->name = "IC";
  info->decl = decl;
  info->is_interface = true;

  info->vtable.push_back({"do_thing", nullptr, info});

  f.ctx.RegisterClassType("IC", info);

  auto* found = f.ctx.FindClassType("IC");
  ASSERT_NE(found, nullptr);
  ASSERT_EQ(found->vtable.size(), 1u);
  EXPECT_EQ(found->vtable[0].method_name, "do_thing");
  EXPECT_EQ(found->vtable[0].method, nullptr);
}

TEST(InterfaceClassSimulation, IsAWithExtendedInterfaces) {
  SimFixture f;

  auto* decl_a = f.arena.Create<ClassDecl>();
  decl_a->name = "IA";
  decl_a->is_interface = true;
  auto* info_a = f.arena.Create<ClassTypeInfo>();
  info_a->name = "IA";
  info_a->decl = decl_a;
  info_a->is_interface = true;
  f.ctx.RegisterClassType("IA", info_a);

  auto* decl_b = f.arena.Create<ClassDecl>();
  decl_b->name = "IB";
  decl_b->is_interface = true;
  auto* info_b = f.arena.Create<ClassTypeInfo>();
  info_b->name = "IB";
  info_b->decl = decl_b;
  info_b->is_interface = true;
  f.ctx.RegisterClassType("IB", info_b);

  auto* decl_c = f.arena.Create<ClassDecl>();
  decl_c->name = "IC";
  decl_c->is_interface = true;
  auto* info_c = f.arena.Create<ClassTypeInfo>();
  info_c->name = "IC";
  info_c->decl = decl_c;
  info_c->is_interface = true;
  info_c->parent = info_a;
  info_c->extended_interfaces.push_back(info_b);
  f.ctx.RegisterClassType("IC", info_c);

  EXPECT_TRUE(info_c->IsA(info_a));
  EXPECT_TRUE(info_c->IsA(info_b));
  EXPECT_TRUE(info_c->IsA(info_c));
  EXPECT_FALSE(info_a->IsA(info_c));
}

}  // namespace
