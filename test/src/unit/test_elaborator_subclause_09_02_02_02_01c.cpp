// §9.2.2.2.1 "Implicit always_comb sensitivities", elaboration side, for the
// reads a block makes through a scope other than its own: a package's
// variable, and what a function reached through a package, a class or a child
// instance reads. The cases drive the inference through ElaborateSrc and read
// RtlirProcess back, as those of test_elaborator_subclause_09_02_02_02_01a.cpp
// do; the line cap in .github/workflows/deltahdl.yml separated them.

#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_sensitivity_assert.h"

using namespace delta;

namespace {

// §9.2.2.2.1 with §26.3: a package's variable read through the package scope
// is a variable the block reads. It is listed as the block spells it and as
// `p.g`, the key the simulator holds a package's variable under, and the bare
// `g`, which names nothing in the module, stays off.
TEST(AlwaysCombScopedReadInference, PackageScopedReadInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  int g;\n"
      "endpackage\n"
      "module t;\n"
      "  int y;\n"
      "  always_comb y = p::g + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"p::g", "p.g"});
}

// §9.2.2.2.1 with §8.23: a class's static method called through the class
// scope is analyzed as any function the block calls. Its read of the class's
// static property joins the list as `C::g`, the name the simulator watches a
// static property by, and its formal stays out. The class's property, its
// method that is not static and its static task enter no function of their
// own.
TEST(AlwaysCombScopedReadInference, ClassStaticMethodReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C;\n"
      "    static int g;\n"
      "    function int nf(); return 0; endfunction\n"
      "    static task st(); endtask\n"
      "    static function int f(int x); return x + g; endfunction\n"
      "  endclass\n"
      "  int a, y;\n"
      "  always_comb y = C::f(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a", "C::g"});
  ExpectSensitivityExcludes(proc, {"g", "x", "C::x"});
}

// §9.2.2.2.1 with §8.23 and §3.12.1: the same for a class the compilation
// unit declares rather than the module.
TEST(AlwaysCombScopedReadInference, UnitClassStaticMethodReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  static int g;\n"
      "  static function int f(int x); return x + g; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a, y;\n"
      "  always_comb y = C::f(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0],
                            {"a", "C::g"});
}

// §9.2.2.2.1 with §23.6: a function of a child instance called by its
// hierarchical name reads the instance's variables, which join the list
// through the instance, `s.g`; its formal stays out. The instance of a
// primitive beside it is of no module and enters no function.
TEST(AlwaysCombScopedReadInference, InstanceFunctionReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "primitive inv(output o, input i);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module sub;\n"
      "  int g;\n"
      "  function int f(int x); return x + g; endfunction\n"
      "endmodule\n"
      "module t;\n"
      "  wire o;\n"
      "  logic i;\n"
      "  inv u(o, i);\n"
      "  sub s();\n"
      "  int a, y;\n"
      "  always_comb y = s.f(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a", "s.g"});
  ExpectSensitivityExcludes(proc, {"g", "x", "s.x"});
}

// §9.2.2.2.1 with §26.3: a package's function calling another function of its
// package by its bare name reaches the package's function, p::h, and not the
// module's own h, and what p::h reads joins the list; its read written through
// the package, `p::g`, is kept as written. The block calls p::h a second time
// itself, which adds nothing new.
TEST(AlwaysCombScopedReadInference, PackageFunctionsBareCallReachesItsPackage) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  int g;\n"
      "  function int h(int x); return x + p::g; endfunction\n"
      "  function int f(int x); return h(x); endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  int a, y, mine;\n"
      "  function int h(int x); return x + mine; endfunction\n"
      "  always_comb y = p::f(a) + p::h(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a", "p.g"});
  ExpectSensitivityExcludes(proc, {"mine", "p::p::g"});
}

}  // namespace
