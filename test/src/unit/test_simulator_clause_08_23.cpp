#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(ClassScopeResolutionSim, ScopeResolutionStaticLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "MyClass", {});
  type->static_properties["MAX_SIZE"] = MakeLogic4VecVal(f.arena, 32, 256);

  auto it = type->static_properties.find("MAX_SIZE");
  ASSERT_NE(it, type->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 256u);
}

TEST(ClassScopeResolutionSim, ScopeResolutionMethodLookup) {
  SimFixture f;
  auto* type = MakeClassType(f, "Utils", {});
  auto* method = f.arena.Create<ModuleItem>();
  method->kind = ModuleItemKind::kFunctionDecl;
  method->name = "compute";
  method->is_static = true;
  type->methods["compute"] = method;

  auto* found = f.ctx.FindClassType("Utils");
  ASSERT_NE(found, nullptr);
  auto it = found->methods.find("compute");
  ASSERT_NE(it, found->methods.end());
  EXPECT_EQ(it->second->name, "compute");
}

TEST(ClassScopeResolutionSim, ScopeResolutionMultipleStaticProps) {
  SimFixture f;
  auto* type = MakeClassType(f, "Config", {});
  type->static_properties["WIDTH"] = MakeLogic4VecVal(f.arena, 32, 8);
  type->static_properties["DEPTH"] = MakeLogic4VecVal(f.arena, 32, 16);

  EXPECT_EQ(type->static_properties["WIDTH"].ToUint64(), 8u);
  EXPECT_EQ(type->static_properties["DEPTH"].ToUint64(), 16u);
}

TEST(ClassScopeResolutionSim, ScopeResolutionMissingProperty) {
  SimFixture f;
  auto* type = MakeClassType(f, "Empty", {});
  auto it = type->static_properties.find("nonexistent");
  EXPECT_EQ(it, type->static_properties.end());
}

TEST(ClassScopeResolutionSim, ScopeResolutionDisambiguates) {
  SimFixture f;
  auto* type = MakeClassType(f, "Base", {});
  type->static_properties["bin"] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* local = f.ctx.CreateLocalVariable("bin", 32);
  local->value = MakeLogic4VecVal(f.arena, 32, 123);

  auto it = type->static_properties.find("bin");
  ASSERT_NE(it, type->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 42u);
  EXPECT_EQ(local->value.ToUint64(), 123u);
}

TEST(ClassScopeResolutionSim, ScopeResolutionBaseClassStatic) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  base->static_properties["count"] = MakeLogic4VecVal(f.arena, 32, 7);

  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto* found = f.ctx.FindClassType("Base");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->static_properties["count"].ToUint64(), 7u);
}

TEST(ClassScopeResolutionSim, ScopeResolutionCallReturnsValue) {
  EXPECT_EQ(RunAndGet(
      "class Util;\n"
      "  static function int answer();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = Util::answer();\n"
      "  end\n"
      "endmodule\n", "result"), 42u);
}

TEST(ClassScopeResolutionSim, StaticPropertyReadViaScope) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  static int count;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = C::count;\n"
      "  end\n"
      "endmodule\n", "result"), 0u);
}

TEST(ClassScopeResolutionSim, StaticPropertyReadWithInit) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  static int val = 99;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = C::val;\n"
      "endmodule\n", "result"), 99u);
}

TEST(ClassScopeResolutionSim, StaticMethodWithArgs) {
  EXPECT_EQ(RunAndGet(
      "class Math;\n"
      "  static function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = Math::add(10, 25);\n"
      "endmodule\n", "result"), 35u);
}

TEST(ClassScopeResolutionSim, StaticVoidMethodCall) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  static int x;\n"
      "  static function void set_x(int v);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  static function int get_x();\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C::set_x(77);\n"
      "    result = C::get_x();\n"
      "  end\n"
      "endmodule\n", "result"), 77u);
}

TEST(ClassScopeResolutionSim, EnumMemberReadViaScope) {
  SimFixture f;
  auto* type = MakeClassType(f, "Base", {});
  type->enum_members["bin"] = 0;
  type->enum_members["oct"] = 1;
  type->enum_members["dec"] = 2;
  type->enum_members["hex"] = 3;

  EXPECT_EQ(type->enum_members["bin"], 0u);
  EXPECT_EQ(type->enum_members["hex"], 3u);
}

TEST(ClassScopeResolutionSim, DisambiguatesClassScopeFromLocal) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  static int val = 42;\n"
      "endclass\n"
      "module t;\n"
      "  int val = 100;\n"
      "  int result;\n"
      "  initial result = Base::val;\n"
      "endmodule\n", "result"), 42u);
}

TEST(ClassScopeResolutionSim, UnknownClassTypeReturnsDefault) {
  SimFixture f;
  auto* found = f.ctx.FindClassType("Nonexistent");
  EXPECT_EQ(found, nullptr);
}

TEST(ClassScopeResolutionSim, NestedClassTypeDistinct) {
  SimFixture f;
  auto* list_type = MakeClassType(f, "StringList", {});
  auto* tree_type = MakeClassType(f, "StringTree", {});

  auto* list_node = MakeClassType(f, "StringList::Node", {});
  list_node->properties.push_back({"name", 32, false});

  auto* tree_node = MakeClassType(f, "StringTree::Node", {});
  tree_node->properties.push_back({"name", 32, false});
  tree_node->properties.push_back({"left", 32, false});

  EXPECT_NE(f.ctx.FindClassType("StringList::Node"),
            f.ctx.FindClassType("StringTree::Node"));
  EXPECT_EQ(list_node->properties.size(), 1u);
  EXPECT_EQ(tree_node->properties.size(), 2u);
  (void)list_type;
  (void)tree_type;
}

TEST(ClassScopeResolutionSim, StaticPropertyLoweredFromDecl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Config;\n"
      "  static int WIDTH = 8;\n"
      "  static int DEPTH = 16;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = Config::WIDTH;\n"
      "    r2 = Config::DEPTH;\n"
      "  end\n"
      "endmodule\n", f);
  LowerRunAndCheck(f, design, {{"r1", 8u}, {"r2", 16u}});
}

TEST(ClassScopeResolutionSim, SuperclassStaticAccessFromDerived) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  static int shared = 55;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  static function int get_shared();\n"
      "    return Base::shared;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = Derived::get_shared();\n"
      "endmodule\n", "result"), 55u);
}

}  // namespace
