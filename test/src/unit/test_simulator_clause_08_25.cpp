#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

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

// §8.25: Each specialization has its own set of static member variables.
TEST(ClassSim, SpecializationsHaveIndependentStaticMembers) {
  SimFixture f;

  auto* typeA = f.arena.Create<ClassTypeInfo>();
  typeA->name = "Vec_8";
  typeA->properties.push_back({"data", 8, false});
  typeA->properties.push_back({"count", 32, true});
  typeA->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 0);
  f.ctx.RegisterClassType("Vec_8", typeA);

  auto* typeB = f.arena.Create<ClassTypeInfo>();
  typeB->name = "Vec_16";
  typeB->properties.push_back({"data", 16, false});
  typeB->properties.push_back({"count", 32, true});
  typeB->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 0);
  f.ctx.RegisterClassType("Vec_16", typeB);

  // Modify static in one specialization.
  typeA->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 42);

  // Other specialization is unaffected.
  EXPECT_EQ(typeA->static_properties["count"].ToUint64(), 42u);
  EXPECT_EQ(typeB->static_properties["count"].ToUint64(), 0u);
}

// §8.25: Multiple params preserved through ClassTypeInfo.
TEST(ClassSim, MultipleParamsPreserved) {
  SimFixture f;

  auto* decl = f.arena.Create<ClassDecl>();
  decl->name = "C";
  decl->params.push_back({"A", nullptr});
  decl->params.push_back({"B", nullptr});
  decl->params.push_back({"C_PARAM", nullptr});

  auto* type = f.arena.Create<ClassTypeInfo>();
  type->name = "C";
  type->decl = decl;
  f.ctx.RegisterClassType("C", type);

  auto* found = f.ctx.FindClassType("C");
  ASSERT_NE(found, nullptr);
  ASSERT_NE(found->decl, nullptr);
  ASSERT_EQ(found->decl->params.size(), 3u);
  EXPECT_EQ(found->decl->params[0].first, "A");
  EXPECT_EQ(found->decl->params[1].first, "B");
  EXPECT_EQ(found->decl->params[2].first, "C_PARAM");
}

// §8.25: Type param names tracked in type_param_names set.
TEST(ClassSim, TypeParamNamesTracked) {
  SimFixture f;

  auto* decl = f.arena.Create<ClassDecl>();
  decl->name = "C";
  decl->params.push_back({"T", nullptr});
  decl->params.push_back({"N", nullptr});
  decl->type_param_names.insert("T");

  auto* type = f.arena.Create<ClassTypeInfo>();
  type->name = "C";
  type->decl = decl;
  f.ctx.RegisterClassType("C", type);

  auto* found = f.ctx.FindClassType("C");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->decl->type_param_names.count("T"));
  EXPECT_FALSE(found->decl->type_param_names.count("N"));
}

// §8.25: Full pipeline — parameterized class lowered with default params.
TEST(ClassSim, LoweredDefaultParamValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C #(parameter int W = 16);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("C");
  ASSERT_NE(info, nullptr);
  // Default param value should be accessible as static property.
  auto it = info->static_properties.find("W");
  ASSERT_NE(it, info->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 16u);
}

// §8.25: Full pipeline — parameterized class with mixed params.
TEST(ClassSim, LoweredMixedParams) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C #(type T = int, parameter int N = 4);\n"
      "    static function int get_n; get_n = N; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("C");
  ASSERT_NE(info, nullptr);
  ASSERT_NE(info->decl, nullptr);
  EXPECT_EQ(info->decl->params.size(), 2u);
  EXPECT_TRUE(info->decl->type_param_names.count("T"));
  EXPECT_FALSE(info->decl->type_param_names.count("N"));
}

// §8.25: Full pipeline — parameterized class extending non-param base.
TEST(ClassSim, LoweredParamClassExtendsBase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class Base;\n"
      "    int x;\n"
      "  endclass\n"
      "  class Derived #(parameter int N = 4) extends Base;\n"
      "    int y;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("Derived");
  ASSERT_NE(info, nullptr);
  EXPECT_NE(info->parent, nullptr);
  EXPECT_EQ(info->parent->name, "Base");
  ASSERT_NE(info->decl, nullptr);
  EXPECT_EQ(info->decl->params.size(), 1u);
}

}  // namespace
