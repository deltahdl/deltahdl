#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

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

TEST(ClassSim, SpecializationsHaveIndependentStaticMembers) {
  SimFixture f;

  auto* type_a = f.arena.Create<ClassTypeInfo>();
  type_a->name = "Vec_8";
  type_a->properties.push_back({"data", 8, false});
  type_a->properties.push_back({"count", 32, true});
  type_a->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 0);
  f.ctx.RegisterClassType("Vec_8", type_a);

  auto* type_b = f.arena.Create<ClassTypeInfo>();
  type_b->name = "Vec_16";
  type_b->properties.push_back({"data", 16, false});
  type_b->properties.push_back({"count", 32, true});
  type_b->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 0);
  f.ctx.RegisterClassType("Vec_16", type_b);

  type_a->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 42);

  EXPECT_EQ(type_a->static_properties["count"].ToUint64(), 42u);
  EXPECT_EQ(type_b->static_properties["count"].ToUint64(), 0u);
}

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

  auto it = info->static_properties.find("W");
  ASSERT_NE(it, info->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 16u);
}

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

// §8.25: a specialization is a generic class combined with a specific set of
// actual parameter values, and instances are declared with the same override
// rules as modules. Two distinct value-parameter specializations of the same
// generic class coexist and each object carries its own parameter value, read
// back here through the full pipeline via instance-qualified access.
TEST(ClassSim, ValueParameterDistinctPerSpecialization) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class vector #(parameter width = 7);\n"
      "  bit [width:0] a;\n"
      "endclass\n"
      "module t;\n"
      "  int w8, w16;\n"
      "  initial begin\n"
      "    vector #(8) v8;\n"
      "    vector #(16) v16;\n"
      "    v8 = new;\n"
      "    v16 = new;\n"
      "    w8 = v8.width;\n"
      "    w16 = v16.width;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"w8", 8u}, {"w16", 16u}});
}

// §8.25: all matching specializations of a generic class shall represent the
// same type. Two variables independently declared with the identical value-
// parameter specialization hold assignment-compatible handles: assigning one to
// the other aliases the same object, so a property written through the first is
// read back through the second. A mismatched type would make the handle
// assignment illegal.
TEST(ClassSim, MatchingSpecializationsAreSameType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class vector #(parameter width = 7);\n"
      "  int data;\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    vector #(4) a;\n"
      "    vector #(4) b;\n"
      "    a = new;\n"
      "    a.data = 55;\n"
      "    b = a;\n"
      "    r = b.data;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 55u}});
}

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

// §8.25: instances use the same override rules as modules, which include named
// parameter overrides. A named override supplies the value the instance reads
// back (the positional form is covered by
// ValueParameterDistinctPerSpecialization).
TEST(ClassSim, NamedParameterOverrideApplied) {
  EXPECT_EQ(RunAndGet("class vector #(parameter width = 7);\n"
                      "  int data;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    vector #(.width(2)) v;\n"
                      "    v = new;\n"
                      "    out = v.width;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2u);
}

// §8.25: a type parameter (here its default, int) determines the type of a
// class property, which is then usable at run time.
TEST(ClassSim, TypeParameterDefaultYieldsUsableProperty) {
  EXPECT_EQ(RunAndGet("class C #(type T = int);\n"
                      "  T data;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.data = 42;\n"
                      "    out = c.data;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            42u);
}

}  // namespace
