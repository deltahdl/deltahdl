#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ClassSim, ParameterizedClassDifferentWidths) {
  SimFixture f;

  auto* type8 = f.arena.Create<ClassTypeInfo>();
  type8->name = "Stack_8";
  type8->properties.push_back({"data", 8, false});
  f.ctx.RegisterClassType("Stack_8", type8);

  auto* type32 = f.arena.Create<ClassTypeInfo>();
  type32->name = "Stack_32";
  type32->properties.push_back({"data", 32, false});
  f.ctx.RegisterClassType("Stack_32", type32);

  auto* t8 = f.ctx.FindClassType("Stack_8");
  auto* t32 = f.ctx.FindClassType("Stack_32");
  ASSERT_NE(t8, nullptr);
  ASSERT_NE(t32, nullptr);
  EXPECT_EQ(t8->properties[0].width, 8u);
  EXPECT_EQ(t32->properties[0].width, 32u);
}

TEST(ClassSim, ParameterizedClassInstantiation) {
  SimFixture f;

  auto* type = f.arena.Create<ClassTypeInfo>();
  type->name = "Pair_int";
  type->properties.push_back({"first", 32, false});
  type->properties.push_back({"second", 32, false});
  f.ctx.RegisterClassType("Pair_int", type);

  auto [handle, obj] = MakeObj(f, type);
  obj->SetProperty("first", MakeLogic4VecVal(f.arena, 32, 10));
  obj->SetProperty("second", MakeLogic4VecVal(f.arena, 32, 20));
  EXPECT_EQ(obj->GetProperty("first", f.arena).ToUint64(), 10u);
  EXPECT_EQ(obj->GetProperty("second", f.arena).ToUint64(), 20u);
}

// §8.25.1: ClassTypeInfo with decl stores param metadata for scope resolution.
TEST(ClassSim, ParameterizedClassDeclParams) {
  SimFixture f;

  auto* decl = f.arena.Create<ClassDecl>();
  decl->name = "C";
  decl->params.push_back({"p", nullptr});

  auto* type = f.arena.Create<ClassTypeInfo>();
  type->name = "C";
  type->decl = decl;
  f.ctx.RegisterClassType("C", type);

  auto* found = f.ctx.FindClassType("C");
  ASSERT_NE(found, nullptr);
  ASSERT_NE(found->decl, nullptr);
  ASSERT_EQ(found->decl->params.size(), 1u);
  EXPECT_EQ(found->decl->params[0].first, "p");
}

// §8.25.1: Static method registered on parameterized class type.
TEST(ClassSim, ParameterizedClassStaticMethod) {
  SimFixture f;

  auto* decl = f.arena.Create<ClassDecl>();
  decl->name = "Codec";
  decl->params.push_back({"W", nullptr});

  auto* type = f.arena.Create<ClassTypeInfo>();
  type->name = "Codec";
  type->decl = decl;

  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "encode";
  method->is_static = true;
  type->methods["encode"] = method;

  f.ctx.RegisterClassType("Codec", type);

  auto* found = f.ctx.FindClassType("Codec");
  ASSERT_NE(found, nullptr);
  auto it = found->methods.find("encode");
  ASSERT_NE(it, found->methods.end());
  EXPECT_TRUE(it->second->is_static);
}

}  // namespace
