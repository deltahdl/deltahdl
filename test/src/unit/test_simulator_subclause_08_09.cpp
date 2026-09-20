#include <gtest/gtest.h>

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

// §8.9 (printed page 186 of ~/LRM.pdf) reaches a static property through the
// class scope resolution operator, and §26.3 (printed 808) reaches a package's
// class through the package scope resolution operator, so `pk::Cfg::depth` is
// the static property of the package's class -- the same storage `Cfg::depth`
// reads after `import pk::Cfg`. The doubly-qualified name was joined into
// "pk.Cfg.depth" and "pk" looked up as a class, which it is not, so the read
// answered 0 while the imported form, `pk::Cfg::two()` and `pk::Cfg::A` were
// right. The result packs the scoped read with the imported one, and a write
// through the scoped form is read back through the imported one.
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

}  // namespace
