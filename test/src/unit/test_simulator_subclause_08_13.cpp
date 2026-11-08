#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "parser/ast_module.h"
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

TEST(InheritanceSimulation, InheritedStaticWrittenThroughDerivedScope) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int n;\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D::n = 3;\n"
                      "    result = C::n * 10 + D::n;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            33u);
}

TEST(InheritanceSimulation, InheritedStaticReadThroughDerivedScope) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int n;\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::n = 5;\n"
                      "    result = D::n;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(InheritanceSimulation, InheritedStaticNamedBareInDerivedStaticMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int n;\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  static function void put(int v);\n"
                      "    n = v;\n"
                      "  endfunction\n"
                      "  static function int get();\n"
                      "    return n;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D::put(6);\n"
                      "    result = C::n * 10 + D::get();\n"
                      "    C::n = 4;\n"
                      "    result = result * 100 + D::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            6604u);
}

TEST(InheritanceSimulation, InheritedStaticSharedThroughBothHandles) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int n;\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    D d;\n"
                      "    c = new;\n"
                      "    d = new;\n"
                      "    d.n = 7;\n"
                      "    result = c.n * 10 + C::n;\n"
                      "    c.n = 8;\n"
                      "    result = result * 100 + d.n;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7708u);
}

TEST(InheritanceSimulation, InheritedStaticHandleReachesItsObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  static C m_inst;\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D d;\n"
                      "    d = new;\n"
                      "    d.k = 4;\n"
                      "    D::m_inst = d;\n"
                      "    result = D::m_inst.k * 10 + C::m_inst.k;\n"
                      "    D::m_inst.k = 5;\n"
                      "    result = result * 100 + d.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            4405u);
}

TEST(InheritanceSimulation, InheritedStaticThroughPackageQualifiedScope) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class C;\n"
                      "    static int n;\n"
                      "  endclass\n"
                      "  class D extends C;\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    p::D::n = 8;\n"
                      "    result = p::C::n * 10 + p::D::n;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            88u);
}

TEST(InheritanceSimulation, ABaseNamedThroughAPackageIsThePackagesClass) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class B;\n"
                      "    int b = 3;\n"
                      "    function int get(); return b * 2; endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  class B;\n"
                      "    int b = 9;\n"
                      "  endclass\n"
                      "  class D extends p::B;\n"
                      "  endclass\n"
                      "  D d = new;\n"
                      "  int result;\n"
                      "  initial result = d.b * 10 + d.get();\n"
                      "endmodule\n",
                      "result"),
            36u);
}

TEST(InheritanceSimulation, InheritedStaticHandleConstructedThroughDerived) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  static C m_inst;\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D::m_inst = new;\n"
                      "    result = C::m_inst.k * 10 + (D::m_inst == null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            90u);
}

TEST(InheritanceSimulation, InheritedStaticHandleNamedBareInDerivedMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  static C m_inst;\n"
                      "  function void add(int v); k = k + v; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function void bump(); m_inst.add(7); endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D d;\n"
                      "    C::m_inst = new;\n"
                      "    d = new;\n"
                      "    d.bump();\n"
                      "    result = C::m_inst.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            16u);
}

TEST(InheritanceSimulation, InheritedStaticFunctionCalledBareInDerivedStatic) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static function int twice(int x);\n"
                      "    return x + x;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  static function int quad(int x);\n"
                      "    return twice(twice(x));\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = D::quad(5);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

TEST(InheritanceSimulation,
     InheritedStaticVoidFunctionWritesDerivedCallersRef) {
  EXPECT_EQ(
      RunAndGet("class Q;\n"
                "  int n = 3;\n"
                "  function int size(); return n; endfunction\n"
                "endclass\n"
                "class C;\n"
                "  static function void m_get_q(ref Q q, input int obj);\n"
                "    q = new;\n"
                "  endfunction\n"
                "endclass\n"
                "class D extends C;\n"
                "  static function int get_first();\n"
                "    Q q;\n"
                "    m_get_q(q, 0);\n"
                "    return q == null ? 7 : q.size();\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    result = D::get_first();\n"
                "  end\n"
                "endmodule\n",
                "result"),
      3u);
}

TEST(InheritedTypedefSim, AStructureMemberNamedByTheBaseTypedefTakesItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [7:0] nib_t;\n"
                       "class Base;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "endclass\n"
                       "class Der extends Base;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1F5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Der d;\n"
                       "  initial begin d = new; d.show(); end\n"
                       "endmodule\n",
                       f),
            "5 10 1\n");
}

TEST(InheritedTypedefSim,
     AStructureMemberNamedByTheBaseTypedefAloneTakesItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Base;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "endclass\n"
                       "class Der extends Base;\n"
                       "  typedef struct packed { nib_t x; logic y; } S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    s = 9'h1F5;\n"
                       "    $display(\"%0d %0d %0d\", $bits(s), s.x, s.y);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Der d;\n"
                       "  initial begin d = new; d.show(); end\n"
                       "endmodule\n",
                       f),
            "5 10 1\n");
}

TEST(InheritedTypedefSim, TheNearestBaseDeclaringTheNameSuppliesTheMember) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Base;\n"
                       "  typedef logic [1:0] nib_t;\n"
                       "  typedef logic [2:0] tri_t;\n"
                       "endclass\n"
                       "class Mid extends Base;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "endclass\n"
                       "class Der extends Mid;\n"
                       "  typedef struct packed { nib_t x; tri_t t; logic y; } "
                       "S;\n"
                       "  S s;\n"
                       "  function void show();\n"
                       "    $display(\"%0d\", $bits(s));\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  Der d;\n"
                       "  initial begin d = new; d.show(); end\n"
                       "endmodule\n",
                       f),
            "8\n");
}

}  // namespace
