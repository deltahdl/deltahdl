#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_sensitivity_assert.h"

using namespace delta;

namespace {

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

TEST(AlwaysCombScopedReadInference, UnitClassStaticMethodReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class E;\n"
      "endclass\n"
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

TEST(AlwaysCombScopedReadInference, DeeperInstanceFunctionReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  int pg;\n"
      "  function int k(int x); return x + pg; endfunction\n"
      "endpackage\n"
      "module leaf;\n"
      "  int g;\n"
      "  function int h(int x); return x + g; endfunction\n"
      "  function int f(int x); return h(x) + p::k(x); endfunction\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf u();\n"
      "  leaf t();\n"
      "endmodule\n"
      "module top;\n"
      "  mid s();\n"
      "  int a, y;\n"
      "  always_comb y = s.t.f(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a", "s.t.g", "p::pg"});
  ExpectSensitivityExcludes(proc, {"g", "x", "s.t.x", "s.u.g"});
}

TEST(AlwaysCombScopedReadInference, TopRootedPathReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  int g;\n"
      "  function int f(int x); return x + g; endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  sub s();\n"
      "  int a, y;\n"
      "  always_comb y = top.s.f(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a", "top.s.g"});
  ExpectSensitivityExcludes(proc, {"g", "x"});
}

TEST(AlwaysCombScopedReadInference, UpwardModuleNameReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  int a, y;\n"
      "  always_comb y = mid.f(a);\n"
      "endmodule\n"
      "module mid;\n"
      "  int g;\n"
      "  function int f(int x); return x + g; endfunction\n"
      "  leaf t();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const auto* mid = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(mid, nullptr);
  const auto* leaf = mid->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  ASSERT_FALSE(leaf->processes.empty());
  const auto& proc = leaf->processes[0];
  ExpectSensitivityContains(proc, {"a", "mid.g"});
  ExpectSensitivityExcludes(proc, {"g", "x"});
}

TEST(AlwaysCombScopedReadInference,
     ClassStaticMethodReadsEnclosingModuleVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int ext, mv, a, y;\n"
      "  function int mf(int x); return x + mv; endfunction\n"
      "  class B;\n"
      "    static int g;\n"
      "  endclass\n"
      "  class D extends B;\n"
      "    static int own;\n"
      "    static function int f(int x);\n"
      "      return x + ext + g + own + mf(x);\n"
      "    endfunction\n"
      "  endclass\n"
      "  always_comb y = D::f(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a", "ext", "mv", "D::g", "D::own"});
  ExpectSensitivityExcludes(proc, {"D::ext", "D::mv", "x", "own"});
}

TEST(AlwaysCombScopedReadInference,
     PackageClassStaticMethodReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package q;\n"
      "  class C;\n"
      "    static int g;\n"
      "    static function int f(int x); return x + g; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "package r;\n"
      "  int z;\n"
      "endpackage\n"
      "package p;\n"
      "  int pv;\n"
      "  function int h(int x); return x + pv; endfunction\n"
      "  class C;\n"
      "    static int g;\n"
      "    static function int f(int x); return h(x) + g; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  int a, y;\n"
      "  always_comb y = p::C::f(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a", "p::C::g", "p::pv"});
  ExpectSensitivityExcludes(proc, {"q::C::g", "g", "x", "pv"});
}

}  // namespace
