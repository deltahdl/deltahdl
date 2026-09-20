#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackageDeclarationSim, VariableInitOccursBeforeInitialProcedure) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  int x = 42;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  int observed;\n"
      "  initial observed = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* observed = f.ctx.FindVariable("observed");
  ASSERT_NE(observed, nullptr);
  EXPECT_EQ(observed->value.ToUint64(), 42u);
}

// §26.2 requires package variable-declaration assignments to complete before
// any initial OR always procedure starts. Here an always_comb procedure samples
// the imported package variable; its initializer must already have run, so the
// captured value is the initialized one.
TEST(PackageDeclarationSim, PackageVariableInitObservedByAlwaysProcedure) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  int seed = 55;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  int captured;\n"
      "  always_comb captured = seed;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* captured = f.ctx.FindVariable("captured");
  ASSERT_NE(captured, nullptr);
  EXPECT_EQ(captured->value.ToUint64(), 55u);
}

// §26.2: a package's declarations are visible by their bare names throughout
// the package, the bodies of the classes it declares included. Each read here
// answered 0 from an instance method before the method's frame carried the
// package: the parameter is 17, the enum literal 8, the function's 5 and the
// variable 42, none of them a value a lost name could give.
TEST(PackageDeclarationSim, PackageClassInstanceMethodReadsPackageNamesBare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int K = 17;\n"
      "  typedef enum { A = 8, B } e_t;\n"
      "  function int five(); return 5; endfunction\n"
      "  int pv = 42;\n"
      "  class Helper;\n"
      "    function int k(); return K; endfunction\n"
      "    function int a(); e_t e = A; return e; endfunction\n"
      "    function int f(); return five(); endfunction\n"
      "    function int v(); return pv; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module top;\n"
      "  int k, a, fv, v;\n"
      "  initial begin\n"
      "    p::Helper h = new;\n"
      "    k = h.k(); a = h.a(); fv = h.f(); v = h.v();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"k", 17u}, {"a", 8u}, {"fv", 5u}, {"v", 42u}});
}

// §26.2 with §8.10: a static method of the package's class reads the package
// parameter by its bare name, as the instance method does; only the `p::K`
// form answered 17 before, the bare one 0 in both.
TEST(PackageDeclarationSim, PackageClassStaticMethodReadsPackageParameterBare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int K = 17;\n"
      "  class Helper;\n"
      "    function int k(); return K; endfunction\n"
      "    function int kq(); return p::K; endfunction\n"
      "    static function int ks(); return K + 100; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module top;\n"
      "  int inst, quals, stat;\n"
      "  initial begin\n"
      "    p::Helper h = new;\n"
      "    inst = h.k(); quals = h.kq(); stat = p::Helper::ks();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"inst", 17u}, {"quals", 17u}, {"stat", 117u}});
}

// §26.2 with §8.24: an out-of-block method body declared in the package stands
// in the package's scope as the class does, so its `K + e` is 50 + 7.
TEST(PackageDeclarationSim, PackageClassOutOfBlockBodyReadsPackageNamesBare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int K = 50;\n"
      "  typedef enum { A = 7, B } e_t;\n"
      "  class C;\n"
      "    extern function int sum();\n"
      "  endclass\n"
      "  function int C::sum();\n"
      "    e_t e = A;\n"
      "    return K + e;\n"
      "  endfunction\n"
      "endpackage\n"
      "module top;\n"
      "  int s;\n"
      "  initial begin\n"
      "    p::C c = new;\n"
      "    s = c.sum();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"s", 57u}});
}

// §26.2 with §8.7: a property initializer of the package's class names the
// package's enum literal bare, so `e` starts at 8 beside the `m` that started
// at 9 already; §8.7's constructor body reads the parameter the same way.
TEST(PackageDeclarationSim,
     PackageClassPropertyInitializerAndNewReadPackageNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int K = 17;\n"
      "  typedef enum { A = 8, B } e_t;\n"
      "  typedef int money_t;\n"
      "  class Holder;\n"
      "    e_t e = A;\n"
      "    money_t m = 9;\n"
      "    int k;\n"
      "    function new(); k = K + 3; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module top;\n"
      "  int e, m, k;\n"
      "  initial begin\n"
      "    p::Holder h = new;\n"
      "    e = h.e; m = h.m; k = h.k;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"e", 8u}, {"m", 9u}, {"k", 20u}});
}

// §26.2: the bare name inside the method is the package's variable itself, so
// a write through it lands in the package's storage: the method's own read
// after the write and the module's `p::pv` both answer 45. Before, the write
// made a property of the object named pv, the method answered 3 and the
// package's variable kept its 42.
TEST(PackageDeclarationSim, PackageClassMethodWritesPackageVariableBare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  int pv = 42;\n"
      "  class Helper;\n"
      "    function int bump(); pv = pv + 3; return pv; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module top;\n"
      "  int ret, after;\n"
      "  initial begin\n"
      "    p::Helper h = new;\n"
      "    ret = h.bump();\n"
      "    after = p::pv;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"ret", 45u}, {"after", 45u}});
}

// §26.2 with §8.23: a class of the compilation unit calling the package class's
// method sees the method read its own package's K, 17, so `a + K` with -16 is
// 1 and the sum with the static square is 50; the caller's `p::K` stays 17.
TEST(PackageDeclarationSim,
     PackageClassMethodCalledFromUnitClassReadsItsOwnPackage) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int K = 17;\n"
      "  class Helper;\n"
      "    static function int sq(int a); return a * a; endfunction\n"
      "    function int addk(int a); return a + K; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "class User;\n"
      "  function int run();\n"
      "    p::Helper h = new;\n"
      "    return p::Helper::sq(7) + h.addk(-16);\n"
      "  endfunction\n"
      "  function int k(); return p::K; endfunction\n"
      "endclass\n"
      "module top;\n"
      "  int r, k;\n"
      "  initial begin\n"
      "    User u = new;\n"
      "    r = u.run(); k = u.k();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"r", 50u}, {"k", 17u}});
}

}  // namespace
