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

TEST(InheritanceSimulation, ASubclassHoldsEveryMemberOfEachClassAboveIt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class G;\n"
      "  int g = 3;\n"
      "  string s = \"ab\";\n"
      "  int q[$] = '{4, 5};\n"
      "  function int gf(); return g * 10; endfunction\n"
      "  task gt(output int o); o = g + 100; endtask\n"
      "endclass\n"
      "class Pa extends G;\n"
      "  int p = 7;\n"
      "  function int pf(); return p + g; endfunction\n"
      "endclass\n"
      "class L extends Pa;\n"
      "  int l = 11;\n"
      "  function int lf(); return g + p + l + gf() + q[1] + s.len(); "
      "endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10;\n"
      "  initial begin\n"
      "    automatic L a = new;\n"
      "    automatic L b = new;\n"
      "    r1 = a.g; r2 = a.p; r3 = a.l; r4 = a.gf(); r5 = a.pf();\n"
      "    r6 = a.lf();\n"
      "    a.gt(r7);\n"
      "    a.g = 20; r8 = a.pf(); r9 = b.g;\n"
      "    r10 = a.q.size() + a.s.len();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 3u},
                    {"r2", 7u},
                    {"r3", 11u},
                    {"r4", 30u},
                    {"r5", 10u},
                    {"r6", 58u},
                    {"r7", 103u},
                    {"r8", 27u},
                    {"r9", 3u},
                    {"r10", 4u}});
}

TEST(InheritanceSimulation, ASubclassInheritsInEveryPlaceAClassIsDeclared) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  class B; int v = 2; function int f(); return v * 3; endfunction "
      "endclass\n"
      "  class D extends B; int w = 5; endclass\n"
      "endpackage\n"
      "class PB #(int N = 1);\n"
      "  int v = N;\n"
      "  function int f(); return v + N; endfunction\n"
      "endclass\n"
      "class PD extends PB #(4); int w = 1; endclass\n"
      "class CD extends pk::B; int w = 6; endclass\n"
      "interface itf;\n"
      "  class IBs; int v = 9; function int f(); return v - 1; endfunction "
      "endclass\n"
      "  class ID extends IBs; endclass\n"
      "  function automatic int t(); ID n = new; return n.f() + n.v; "
      "endfunction\n"
      "endinterface\n"
      "program pr(output int o);\n"
      "  class RB; int v = 12; function int f(); return v * 2; endfunction "
      "endclass\n"
      "  class RD extends RB; endclass\n"
      "  initial begin automatic RD n = new; o = n.f() + n.v; end\n"
      "endprogram\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5, r6, r7;\n"
      "  itf i();\n"
      "  pr p(r7);\n"
      "  class MB; int v = 13; function int f(); return v + 2; endfunction "
      "endclass\n"
      "  class MD extends MB; endclass\n"
      "  if (1) begin : g\n"
      "    class GB; int v = 14; function int f(); return v + 3; "
      "endfunction endclass\n"
      "    class GD extends GB; endclass\n"
      "    function automatic int t(); GD n = new; return n.f() + n.v; "
      "endfunction\n"
      "  end\n"
      "  initial begin\n"
      "    automatic pk::D d = new;\n"
      "    automatic PD pd = new;\n"
      "    automatic CD cd = new;\n"
      "    automatic MD md = new;\n"
      "    r1 = d.f() + d.v + d.w;\n"
      "    r2 = pd.f() + pd.v + pd.w;\n"
      "    r3 = cd.f() + cd.w;\n"
      "    r4 = i.t();\n"
      "    r5 = md.f() + md.v;\n"
      "    r6 = g.t();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 13u},
                    {"r2", 13u},
                    {"r3", 12u},
                    {"r4", 17u},
                    {"r5", 28u},
                    {"r6", 31u},
                    {"r7", 36u}});
}

TEST(InheritanceSimulation,
     DISABLED_ASubclassInheritsFromANestedSiblingOrATypedefNamedBase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class G; int v = 5; function int f(); return v + 1; endfunction "
      "endclass\n"
      "class Out;\n"
      "  class NB; int v = 8; function int f(); return v + 1; endfunction "
      "endclass\n"
      "  class ND extends NB; int w = 2; endclass\n"
      "  class NG extends G; endclass\n"
      "  static function int t(); ND n = new; return n.f() + n.v; "
      "endfunction\n"
      "endclass\n"
      "typedef G GT;\n"
      "class X extends GT; endclass\n"
      "class PB #(int N = 1); int v = N; endclass\n"
      "typedef PB #(6) PT;\n"
      "class Y extends PT; endclass\n"
      "package pk;\n"
      "  class B; int v = 3; endclass\n"
      "  typedef B BT;\n"
      "endpackage\n"
      "class Z extends pk::BT; endclass\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8;\n"
      "  typedef G MT;\n"
      "  class W extends MT; endclass\n"
      "  initial begin\n"
      "    automatic Out::ND a = new;\n"
      "    automatic Out::NG b = new;\n"
      "    automatic X c = new;\n"
      "    automatic Y d = new;\n"
      "    automatic Z e = new;\n"
      "    automatic W w = new;\n"
      "    r1 = Out::t();\n"
      "    r2 = a.v + a.w;\n"
      "    r3 = b.f();\n"
      "    r4 = c.f();\n"
      "    r5 = c.v;\n"
      "    r6 = d.v;\n"
      "    r7 = e.v;\n"
      "    r8 = w.f();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 17u},
                    {"r2", 10u},
                    {"r3", 6u},
                    {"r4", 6u},
                    {"r5", 5u},
                    {"r6", 6u},
                    {"r7", 3u},
                    {"r8", 6u}});
}

TEST(InheritanceSimulation,
     AnOwnParameterInALocalparamAndAnInheritedOneInAMethodAreRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class D;\n"
      "  parameter int N = 5;\n"
      "endclass\n"
      "class E extends D;\n"
      "  static function int t(); return N * 2; endfunction\n"
      "endclass\n"
      "class Own;\n"
      "  parameter int Q = 2;\n"
      "  localparam V = Q + 1;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = E::t();\n"
      "    r2 = Own::V;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 3u}});
}

TEST(InheritanceSimulation,
     DISABLED_AnInheritedParameterGivesALocalparamAndARangeItsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class D;\n"
      "  parameter int N = 5;\n"
      "  localparam int M = 7;\n"
      "  parameter logic [1:0][3:0] DQ = 8'h6c;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } st;\n"
      "  parameter st SP = '{4'h3, 4'h9};\n"
      "endclass\n"
      "class E extends D;\n"
      "  localparam V1 = N + 1, V2 = M, V3 = DQ[1], V4 = SP.b, V5 = N;\n"
      "  logic [N-1:0] w;\n"
      "endclass\n"
      "class F #(int P = 3) extends D;\n"
      "  localparam V6 = N + P;\n"
      "endclass\n"
      "class G extends F #(4);\n"
      "  localparam V7 = P * 2;\n"
      "endclass\n"
      "class H extends G;\n"
      "  localparam V8 = N + P + M;\n"
      "endclass\n"
      "interface class IA;\n"
      "  parameter int IN = 5;\n"
      "endclass\n"
      "interface class IB extends IA;\n"
      "  localparam V9 = IN + 1;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10;\n"
      "  initial begin\n"
      "    automatic E e = new;\n"
      "    r1 = E::V1; r2 = E::V2; r3 = E::V3; r4 = E::V4; r5 = E::V5;\n"
      "    r6 = $bits(e.w); r7 = F#()::V6; r8 = G::V7; r9 = H::V8;\n"
      "    r10 = IB::V9;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r1", 6u},
                    {"r2", 7u},
                    {"r3", 6u},
                    {"r4", 9u},
                    {"r5", 5u},
                    {"r6", 5u},
                    {"r7", 8u},
                    {"r8", 8u},
                    {"r9", 16u},
                    {"r10", 6u}});
}

}  // namespace
