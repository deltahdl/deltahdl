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

// §8.13 (printed pages 189-190) with §8.9 (printed 186): a derived class
// inherits the base's properties, and a static property is one storage
// shared by every object of its class, so `D::n` and `C::n` name C's one
// storage. Written through D and read through both, 3 * 10 + 3; the write
// found no slot in D's own static_properties and landed nowhere, and each
// read 0.
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

// §8.13 with §8.9: the same storage the other way about -- written through
// the base's scope and read through the derived one, 5 where `D::n` read 0
// from D's own static_properties, which hold D's declarations alone.
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

// §8.13 with §8.10 (printed page 186): a static method of D names the
// inherited static property bare, and both its write and its read are of
// C's one storage: put(6) makes `C::n` 6 and get() reads it, 66; then
// `C::n = 4` is what get() reads, 6604. The bare write landed nowhere and
// the bare read gave 0, D's own static_properties holding no `n`.
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

// §8.13 with §8.9: `d.n` through a D handle and `c.n` through a C handle
// read and write the one storage, as `C::n` does: `d.n = 7` read back as 77
// through c.n and C::n, then `c.n = 8` read back as 8 through d.n, 7708. The
// write through d landed in the D object's own map, where only d.n saw it.
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

// §8.13 with §8.9 and §8.4 (printed pages 181-182): a static handle C
// declares is reached as `D::m_inst`, and a member through it is the
// object's: after `d.k = 4` and `D::m_inst = d`, `D::m_inst.k` and
// `C::m_inst.k` both read 4, 44; `D::m_inst.k = 5` writes d's k, 4405.
// Asked of D's own static_properties, the base named no static property,
// so the read gave x and the write went nowhere.
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

// §8.13 with §8.9 and §26.3 (printed page 810): the same one storage for a
// package's classes, written as `p::D::n` and read back through `p::C::n`
// and `p::D::n`, 88 where each read 0.
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

// §8.13 with §8.9 and §8.7 (printed page 184): `D::m_inst = new` constructs
// into the static handle C declares, so `C::m_inst.k` reads the new object's
// 9 and `D::m_inst == null` reads 0, 90; declined for D's own
// static_properties, the handle stayed null and the read gave x.
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

// §8.13 with §8.10 and §8.6 (printed page 183): the bare `m_inst` of D's
// instance method is the static handle C declares, so `m_inst.add(7)` runs
// on the object `C::m_inst` holds and its k reads 16 through `C::m_inst.k`;
// read from D's own static_properties, the bare name gave the null handle
// and the call was reported.
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

// §8.13 (printed pages 189-190) with §8.10 (printed 186-187): a subclass
// inherits the base's methods, static ones among them, and a static method
// runs with no `this`, so a static method of D calling C's static function
// bare calls C's, in class scope. D::quad(5) is twice(twice(5)), 20. Looked
// up in D's own methods alone, the call ran nothing and yielded 0.
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

// §8.13 with §8.10 and §13.5.2 (printed page 348): the inherited static
// function may be void and take a ref formal, as uvm_typed_callbacks'
// m_get_q does for uvm_callbacks' get_first, and the write through the ref
// reaches the caller's local: get_first's q holds the object m_get_q
// constructed, whose size reads 3. The call ran nothing, q stayed null, and
// the size call through it was reported.
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

}  // namespace
