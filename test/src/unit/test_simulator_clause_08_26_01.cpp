#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassSim, InterfaceClassTypeInfoFlag) {
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

TEST(ClassSim, InterfaceClassVtableEntries) {
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

}  // namespace
