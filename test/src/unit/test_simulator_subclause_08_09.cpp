#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §8.9: a static class property is a single shared copy. A write performed
// through one handle is observed through a different handle of the same type,
// because both resolve to the one shared storage cell rather than to a
// per-instance copy.
TEST(StaticClassPropertySim, SharedAcrossInstancesViaHandle) {
  EXPECT_EQ(RunAndGet("class Counter;\n"
                      "  static int count;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Counter a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.count = 7;\n"
                      "    result = b.count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

// §8.9: a static property is shared, so a value written through a handle is the
// same value read back through that same handle -- the write reaches the shared
// cell, and the read must return the shared cell (not a stale instance copy).
TEST(StaticClassPropertySim, WriteThenReadBackViaSameHandle) {
  EXPECT_EQ(RunAndGet("class Counter;\n"
                      "  static int count;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Counter a;\n"
                      "    a = new;\n"
                      "    a.count = 21;\n"
                      "    result = a.count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            21u);
}

// §8.9: the static property is created and initialized once. Constructing a
// fresh object of the type does not re-run the initializer, so a value written
// into the shared cell survives a later construction.
TEST(StaticClassPropertySim, InitializedOnceSurvivesReconstruction) {
  EXPECT_EQ(RunAndGet("class Counter;\n"
                      "  static int count = 5;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Counter a;\n"
                      "    a = new;\n"
                      "    a.count = 20;\n"
                      "    a = new;\n"
                      "    result = a.count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

// §8.9: static class properties can be used without creating an object of that
// type. The declaration initializer is applied once at start of simulation, so
// the value is observable through class-scope resolution with no instance.
TEST(StaticClassPropertySim, InitializerValueReadWithoutObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int base = 42;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C::base;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

// §8.9: a static property with no explicit initializer is created and
// initialized (to the default zero) once, and is readable without an instance.
TEST(StaticClassPropertySim, ZeroInitializedReadWithoutObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int s;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = 100 + C::s;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            100u);
}

// §8.9: static class properties can be written and read through class-scope
// resolution with no object of the type ever created.
TEST(StaticClassPropertySim, WriteAndReadWithoutObjectViaScope) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int x;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::x = 99;\n"
                      "    result = C::x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            99u);
}

// §8.9: the same shared cell backs both access forms. A scope-qualified write
// is visible through an instance handle...
TEST(StaticClassPropertySim, ScopeWriteVisibleViaHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int s;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a;\n"
                      "    a = new;\n"
                      "    C::s = 33;\n"
                      "    result = a.s;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            33u);
}

// ...and an instance-qualified write is visible through class-scope resolution.
TEST(StaticClassPropertySim, HandleWriteVisibleViaScope) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int s;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a;\n"
                      "    a = new;\n"
                      "    a.s = 44;\n"
                      "    result = C::s;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            44u);
}

// §8.9 negative form: a non-static (instance) property is NOT shared. Each
// object owns its own copy, so a write through one handle is not observed
// through another -- this is exactly the behavior the static keyword changes.
TEST(StaticClassPropertySim, InstancePropertyNotShared) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int v;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.v = 7;\n"
                      "    result = b.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

// §8.9 sharing across data types (§8.5 admits any property type): a
// packed-vector static property is one shared cell of the declared width, so a
// handle write is observed at full 8-bit width through a different handle.
TEST(StaticClassPropertySim, SharedPackedVectorAcrossInstances) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static bit [7:0] count;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.count = 8'hAB;\n"
                      "    result = b.count;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0xABu);
}

// §8.9 sharing with a string-typed static property: the string written through
// one handle is the same string read through another.
TEST(StaticClassPropertySim, SharedStringAcrossInstances) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static string name;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C a, b;\n"
                      "    a = new;\n"
                      "    b = new;\n"
                      "    a.name = \"hello\";\n"
                      "    result = (b.name == \"hello\") ? 100 : 0;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            100u);
}

// §8.9 sharing with a real-typed static property: the real value written
// through one handle is shared and read back through another.
TEST(StaticClassPropertySim, SharedRealAcrossInstances) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("class C;\n"
                                 "  static real r;\n"
                                 "endclass\n"
                                 "module t;\n"
                                 "  real out;\n"
                                 "  initial begin\n"
                                 "    C a, b;\n"
                                 "    a = new;\n"
                                 "    b = new;\n"
                                 "    a.r = 3.5;\n"
                                 "    out = b.r;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "out"),
                   3.5);
}

// §8.9 C3 with a non-default width: a static property is created and
// initialized once from its literal initializer, and the full-width value is
// observable through class-scope resolution with no instance created.
TEST(StaticClassPropertySim, VectorInitializerReadWithoutObject) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static bit [7:0] x = 8'hFF;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C::x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0xFFu);
}

// §8.9 with §7.10: a static property declared with a queue dimension is one
// queue of the class, which every constructor's `all.push_back(this)` grows
// and `Reg::all.size()` counts from the module: two objects, and the second
// element the object whose id is 5 (§8.4, a queue of handles).
TEST(StaticClassPropertySim, StaticQueuePropertyPushedFromConstructors) {
  EXPECT_EQ(RunAndGet("class Reg;\n"
                      "  static Reg all[$];\n"
                      "  int id;\n"
                      "  function new(int i);\n"
                      "    id = i;\n"
                      "    all.push_back(this);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    Reg a = new(3);\n"
                      "    Reg b = new(5);\n"
                      "    out = Reg::all.size() * 10 + Reg::all[1].id;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            25u);
}

// §8.9 (printed page 186 of IEEE 1800-2023) reaches a static property
// through the class scope resolution operator, and §26.3 (printed 808) reaches
// a package's class through the package scope resolution operator, so
// `pk::Cfg::depth` is the static property of the package's class -- the same
// storage `Cfg::depth` reads after `import pk::Cfg`. The doubly-qualified name
// was joined into "pk.Cfg.depth" and "pk" looked up as a class, which it is
// not, so the read answered 0 while the imported form, `pk::Cfg::two()` and
// `pk::Cfg::A` were right. The result packs the scoped read with the imported
// one, and a write through the scoped form is read back through the imported
// one.
TEST(StaticClassPropertySim, StaticPropertyThroughAPackageQualifiedClassScope) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  class Cfg;\n"
                      "    static int depth = 3;\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import pk::Cfg;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = pk::Cfg::depth * 10 + Cfg::depth;\n"
                      "    pk::Cfg::depth = 7;\n"
                      "    result = result * 100 + Cfg::depth;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3307u);
}

// §8.9 with §26.3: the same read with no import written, the package's class
// named through its scope alone.
TEST(StaticClassPropertySim, StaticPropertyThroughAPackageQualifiedScopeAlone) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  class Cfg;\n"
                      "    static int depth = 3;\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = pk::Cfg::depth + 40;\n"
                      "endmodule\n",
                      "result"),
            43u);
}

// §8.9 (printed page 186) with §6.21 (printed 132-133): a static property's
// one copy takes its initializer at the static initialization, an
// expression of the class's declaring scope in which the module's own `int
// K = 3` is a declaration in scope, so `C::s` of the module's `class C;
// static int s = K;` is 3. Lowerer::LowerModule (lowerer.cpp) evaluated the
// module's classes' static initializers as it registered the classes, ahead
// of the module's variables, so K was read before LowerVar had given it 3:
// 0. A unit's or a package's K was already right, the design data being
// constructed ahead of every module.
TEST(StaticClassPropertySim, ModuleStaticInitializerReadsTheModulesVariable) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int K = 3;\n"
                      "  class C;\n"
                      "    static int s = K;\n"
                      "  endclass\n"
                      "  int result;\n"
                      "  initial result = C::s;\n"
                      "endmodule\n",
                      "result"),
            3u);
}

// §8.9 with §15.4.1 (printed 374) and §15.4.4 (printed 375): the module's
// `static mailbox mb = new(K)` is built once at the static initialization
// with the bound the module's `int K = 1` gives, so the first try_put()
// places its message, 1, and the second finds the queue full, 0: 10. Built
// as the class was registered, the mailbox read K as 0, unbounded, and both
// placed: 11.
TEST(StaticClassPropertySim, ModuleStaticMailboxBoundByTheModulesVariable) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  int K = 1;\n"
                "  class C;\n"
                "    static mailbox mb = new(K);\n"
                "  endclass\n"
                "  int result;\n"
                "  initial result = C::mb.try_put(1) * 10 + C::mb.try_put(2);\n"
                "endmodule\n",
                "result"),
      10u);
}

// §8.9 (printed page 186) with §8.4 (printed 181-182): a static property is
// one variable shared by every object and usable with no object, and a
// property of an object is read through any handle to it -- the handle
// `C::m_inst` holds included. The module stores its own object in the
// static property and reads `C::m_inst.k` beside the null test, 9 for the
// object's k. EvalMemberAccess flattened the path to "C.m_inst.k" and parted
// it at the class, "C" and "m_inst.k", a static property nothing is named,
// so the read was x and printed 0 while `C::m_inst == null` was right.
TEST(StaticClassPropertySim, PropertyReadThroughTheClassScopedStaticHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  static C m_inst;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    C::m_inst = c;\n"
                      "    result = (C::m_inst == null) * 100 + C::m_inst.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            9u);
}

// §8.9 with §8.4: the write side of the same access, `C::m_inst.k = 4`,
// lands on the object the static handle refers to, read back through the
// module's own handle to it, and a chained member `C::m_inst.kid.k` reads
// through a second handle the object holds. The flattened "C.m_inst" named
// no variable, so the write went nowhere and c.k stayed 9; the chained read
// was x.
TEST(StaticClassPropertySim, PropertyWrittenThroughTheClassScopedStaticHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  C kid;\n"
                      "  static C m_inst;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    c.kid = new;\n"
                      "    C::m_inst = c;\n"
                      "    C::m_inst.k = 4;\n"
                      "    result = c.k * 10 + C::m_inst.kid.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            49u);
}

// §8.10 (printed page 186): a static method accesses the static properties
// of its class directly, by the bare name, and §8.4 reads a member of the
// object one of them refers to through it. The static method constructs the
// object into m_inst and reads `m_inst.k`, 9, where copying to a local first
// already read 9. A bare base was resolved through the running object's
// properties alone (TryImplicitThisHandleMember), and a static method runs
// on none, so the read fell through to x and printed 0.
TEST(StaticClassPropertySim, StaticMethodReadsAPropertyThroughItsStaticHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  static C m_inst;\n"
                      "  static function int k_via_static();\n"
                      "    if (m_inst == null) m_inst = new;\n"
                      "    return m_inst.k;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C::k_via_static();\n"
                      "endmodule\n",
                      "result"),
            9u);
}

// §8.10 with §8.6 (printed page 183): a method is called through any handle
// to the object, so the static method's `m_inst.add(7)` runs add on the
// object m_inst holds, which adds 7 to its k, and `m_inst.k = m_inst.k + 20`
// writes the same property through the same handle: 9 + 7 + 20. Resolved by
// the shaped arms alone -- a variable's handle, a running object's property
// -- the bare base with no `this` reached no object, so the call fell to the
// module's functions and the write went nowhere; the copy to a local read 9.
TEST(StaticClassPropertySim, StaticMethodCallsAndWritesThroughItsStaticHandle) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 9;\n"
                      "  static C m_inst;\n"
                      "  function void add(int v); k = k + v; endfunction\n"
                      "  static function int go();\n"
                      "    C c;\n"
                      "    if (m_inst == null) m_inst = new;\n"
                      "    m_inst.add(7);\n"
                      "    m_inst.k = m_inst.k + 20;\n"
                      "    c = m_inst;\n"
                      "    return c.k;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C::go();\n"
                      "endmodule\n",
                      "result"),
            36u);
}

// §8.9 with §26.3 (printed page 810): the same three accesses on a class a
// package declares -- the static method's bare `m_inst.add(7)` and
// `m_inst.k`, and the module's `p::C::m_inst.k` through the package scope
// after the method has built the object -- which is uvm_domain.svh:189's
// `m_uvm_domain.add(...)` after `m_uvm_domain = new("uvm")`. Each read 0 and
// the add wrote nothing; 16 from the method, then 16 again through the
// package-qualified scope.
TEST(StaticClassPropertySim, PackageClassStaticHandleReachesItsObject) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class C;\n"
                      "    int k = 9;\n"
                      "    static C m_inst;\n"
                      "    function void add(int v); k = k + v; endfunction\n"
                      "    static function int go();\n"
                      "      if (m_inst == null) begin\n"
                      "        m_inst = new;\n"
                      "        m_inst.add(7);\n"
                      "      end\n"
                      "      return m_inst.k;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C::go() * 100;\n"
                      "    result = result + p::C::m_inst.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1616u);
}

// §8.9 with §8.20 (printed page 196): the static handle is declared with the
// base class, so a non-virtual method called through it is the base's own
// even where the object is of the derived class, while a virtual one is the
// derived class's override -- the declared class the static property's
// declaration names decides the dispatch, as a variable's declared class
// does. The base's who() answers 1, the derived's 2; the virtual tag()
// answers 20 from the override: 1 * 100 + 20.
TEST(StaticClassPropertySim, StaticHandleDispatchesByItsDeclaredClass) {
  EXPECT_EQ(RunAndGet("class B;\n"
                      "  static B m_inst;\n"
                      "  function int who(); return 1; endfunction\n"
                      "  virtual function int tag(); return 10; endfunction\n"
                      "endclass\n"
                      "class D extends B;\n"
                      "  function int who(); return 2; endfunction\n"
                      "  virtual function int tag(); return 20; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    D d;\n"
                      "    d = new;\n"
                      "    B::m_inst = d;\n"
                      "    result = B::m_inst.who() * 100 + B::m_inst.tag();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            120u);
}

// §8.9 with §6.8 (Table 6-7, printed page 107): a static property with no
// initializer takes its type's default -- 'x for a 4-state logic or vector,
// 0 for a 2-state int -- as the instance property of the same class does,
// whether read through the class scope or through a handle. The static
// logic read 0 while the instance logic beside it read x.
TEST(StaticClassPropertySim, Uninitialized4StateStaticReadsX) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  class C;\n"
                 "    logic l;\n"
                 "    static logic sl; static logic [3:0] sv;\n"
                 "    static int sn;\n"
                 "  endclass\n"
                 "  C c;\n"
                 "  initial begin\n"
                 "    c = new;\n"
                 "    $display(\"l=%0h sl=%0h sv=%b sn=%0d hsl=%0h\", c.l,\n"
                 "             C::sl, C::sv, C::sn, c.sl);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "l=x sl=x sv=xxxx sn=0 hsl=x\n");
}

// §8.9 (printed page 186) with §8.7: a static property named through a
// handle, `m_t_inst.m_tw`, is the class's one storage, and a bare `new`
// assigned to it constructs an object of the property's declared class into
// that storage: `m_t_inst.m_tw = new` in init(), m_t_inst itself a static
// handle, is what uvm_typed_callbacks#(T)::m_initialize does with
// `m_t_inst.m_tw_cb_q = new("typewide_queue")`, and `C::m_tw.k` then reads
// the constructed Q's 3. The base of the `new` was taken for a variable or
// a class name alone, so the static handle named neither, the `new` was
// read as a value, and C::m_tw stayed null, 7.
TEST(StaticClassPropertySim, NewAssignedToAStaticThroughAStaticHandle) {
  EXPECT_EQ(RunAndGet("class Q;\n"
                      "  int k = 3;\n"
                      "endclass\n"
                      "class C;\n"
                      "  static C m_t_inst;\n"
                      "  static Q m_tw;\n"
                      "  static function void init();\n"
                      "    m_t_inst = new;\n"
                      "    m_t_inst.m_tw = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::init();\n"
                      "    result = C::m_tw == null ? 7 : C::m_tw.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

// §8.9 with §8.4: the same target written a handle, `m_t_inst.m_tw = q`,
// lands in the class's storage, which `C::m_tw` reads as q's k of 5. The
// write through the static handle landed in the object's own property map,
// where no read of C::m_tw looked, 7.
TEST(StaticClassPropertySim, ValueAssignedToAStaticThroughAStaticHandle) {
  EXPECT_EQ(RunAndGet("class Q;\n"
                      "  int k = 3;\n"
                      "endclass\n"
                      "class C;\n"
                      "  static C m_t_inst;\n"
                      "  static Q m_tw;\n"
                      "  static function void init();\n"
                      "    Q q = new;\n"
                      "    q.k = 5;\n"
                      "    m_t_inst = new;\n"
                      "    m_t_inst.m_tw = q;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C::init();\n"
                      "    result = C::m_tw == null ? 7 : C::m_tw.k;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

// §8.9 (printed page 186) with §8.10 (printed 186-187): a static method
// names its class's static handle bare and calls through it, `m_t.k()` in
// C::via(), whatever object the method that called it was running on --
// here Other's go(), whose object C's static is no property of. The call
// answers the Q's 4 and reports nothing. The handle was read off the
// calling method's object by its class, Other, which declares no m_t, so
// the call was reported as made through a null handle and then run.
TEST(StaticClassPropertySim,
     StaticMethodCallsThroughItsStaticHandleUnderAnotherClassesMethod) {
  EXPECT_EQ(
      RunAndGet("class Q;\n"
                "  function int k(); return 4; endfunction\n"
                "endclass\n"
                "class C;\n"
                "  static Q m_t;\n"
                "  static function int via(); return m_t.k(); endfunction\n"
                "endclass\n"
                "class Other;\n"
                "  function int go();\n"
                "    C::m_t = new;\n"
                "    return C::via();\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  int result;\n"
                "  initial begin\n"
                "    Other o = new;\n"
                "    result = o.go();\n"
                "  end\n"
                "endmodule\n",
                "result"),
      4u);
}

}  // namespace
