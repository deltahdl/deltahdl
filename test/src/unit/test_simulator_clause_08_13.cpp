#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(InheritanceSimulation, InheritanceParentLink) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {"x"});
  auto* derived = MakeClassType(f, "Derived", {"y"});
  derived->parent = base;

  EXPECT_EQ(derived->parent, base);
  EXPECT_EQ(derived->parent->name, "Base");
}

TEST(InheritanceSimulation, InheritanceChainPropertyAccess) {
  SimFixture f;
  auto* grand = MakeClassType(f, "Grand", {"a"});
  auto* parent = MakeClassType(f, "Parent", {"b"});
  parent->parent = grand;
  auto* child = MakeClassType(f, "Child", {"c"});
  child->parent = parent;

  auto [handle, obj] = MakeObj(f, child);
  obj->SetProperty("a", MakeLogic4VecVal(f.arena, 32, 1));
  obj->SetProperty("b", MakeLogic4VecVal(f.arena, 32, 2));
  obj->SetProperty("c", MakeLogic4VecVal(f.arena, 32, 3));

  EXPECT_EQ(obj->GetProperty("a", f.arena).ToUint64(), 1u);
  EXPECT_EQ(obj->GetProperty("b", f.arena).ToUint64(), 2u);
  EXPECT_EQ(obj->GetProperty("c", f.arena).ToUint64(), 3u);
}

TEST(InheritanceSimulation, MethodResolutionWalksChain) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* mid = MakeClassType(f, "Mid", {});
  mid->parent = base;
  auto* leaf = MakeClassType(f, "Leaf", {});
  leaf->parent = mid;

  auto* m = f.arena.Create<ModuleItem>();
  m->kind = ModuleItemKind::kFunctionDecl;
  m->name = "deep_method";
  base->methods["deep_method"] = m;

  auto [handle, obj] = MakeObj(f, leaf);
  auto* resolved = obj->ResolveMethod("deep_method");
  EXPECT_EQ(resolved, m);
}

TEST(InheritanceSimulation, IsAReflexive) {
  SimFixture f;
  auto* type = MakeClassType(f, "A", {});
  EXPECT_TRUE(type->IsA(type));
}

TEST(InheritanceSimulation, IsADerived) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  EXPECT_TRUE(derived->IsA(base));
  EXPECT_FALSE(base->IsA(derived));
}

TEST(InheritanceSimulation, IsAMultiLevel) {
  SimFixture f;
  auto* a = MakeClassType(f, "A", {});
  auto* b = MakeClassType(f, "B", {});
  b->parent = a;
  auto* c = MakeClassType(f, "C", {});
  c->parent = b;

  EXPECT_TRUE(c->IsA(a));
  EXPECT_TRUE(c->IsA(b));
  EXPECT_FALSE(a->IsA(c));
}

TEST(InheritanceSimulation, IsAUnrelatedTypes) {
  SimFixture f;
  auto* a = MakeClassType(f, "A", {});
  auto* b = MakeClassType(f, "B", {});

  EXPECT_FALSE(a->IsA(b));
  EXPECT_FALSE(b->IsA(a));
}

// §8.13: once a subclass extends a base class, all of the base class's
// properties and methods become part of the subclass. Built from real `extends`
// source and driven through the full pipeline, an object of the derived class
// both reads a property declared only in the base and calls a method declared
// only in the base.
TEST(InheritanceSimulation, DerivedInheritsBasePropertyAndMethod) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  int bval;\n"
      "  function int base_get();\n"
      "    return 7;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  int dval;\n"
      "endclass\n"
      "module t;\n"
      "  int p, m;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    d.bval = 42;\n"
      "    p = d.bval;\n"
      "    m = d.base_get();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"p", 42u}, {"m", 7u}});
}

// §8.13: the methods of the base class can be overridden to change their
// definitions. A call on a derived-class handle to a name the derived class
// redefines resolves to the derived definition (1 from the base would show no
// override took effect).
TEST(InheritanceSimulation, DerivedMethodOverridesBaseFullPipeline) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  function int who();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int who();\n"
      "    return 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    r = d.who();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r", 2u}});
}

TEST(InheritanceSimulation, MethodNotFoundReturnsNull) {
  SimFixture f;
  auto* base = MakeClassType(f, "Base", {});
  auto* derived = MakeClassType(f, "Derived", {});
  derived->parent = base;

  auto [handle, obj] = MakeObj(f, derived);
  EXPECT_EQ(obj->ResolveMethod("nonexistent"), nullptr);
}

// §8.13: inheritance carries over methods of every kind, not just functions. A
// task declared only in the base is callable on a derived object and operates
// on the inherited property.
TEST(InheritanceSimulation, DerivedInheritsBaseTask) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  int v;\n"
      "  task setit();\n"
      "    v = 33;\n"
      "  endtask\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "endclass\n"
      "module t;\n"
      "  int out;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    d.setit();\n"
      "    out = d.v;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"out", 33u}});
}

// §8.13: a base task can also be overridden by the derived class; a call on a
// derived handle runs the derived definition (1 would mean the base version
// ran).
TEST(InheritanceSimulation, DerivedOverridesBaseTask) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class Base;\n"
      "  int v;\n"
      "  task setit();\n"
      "    v = 1;\n"
      "  endtask\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  task setit();\n"
      "    v = 2;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int out;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    d.setit();\n"
      "    out = d.v;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"out", 2u}});
}

}  // namespace
