#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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
      "    static p::Helper h = new;\n"
      "    k = h.k(); a = h.a(); fv = h.f(); v = h.v();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"k", 17u}, {"a", 8u}, {"fv", 5u}, {"v", 42u}});
}

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
      "    static p::Helper h = new;\n"
      "    inst = h.k(); quals = h.kq(); stat = p::Helper::ks();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"inst", 17u}, {"quals", 17u}, {"stat", 117u}});
}

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
      "    static p::C c = new;\n"
      "    s = c.sum();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"s", 57u}});
}

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
      "    static p::Holder h = new;\n"
      "    e = h.e; m = h.m; k = h.k;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"e", 8u}, {"m", 9u}, {"k", 20u}});
}

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
      "    static p::Helper h = new;\n"
      "    ret = h.bump();\n"
      "    after = p::pv;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"ret", 45u}, {"after", 45u}});
}

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
      "    static User u = new;\n"
      "    r = u.run(); k = u.k();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"r", 50u}, {"k", 17u}});
}

static uint64_t PackageClassReadBesideTheTopsG(const std::string& class_body,
                                               const std::string& read) {
  return RunAndGet(
      "package p;\n"
      "  int g = 5;\n"
      "  class C;\n" +
          class_body +
          "  endclass\n"
          "endpackage\n"
          "module top;\n"
          "  int g = 7;\n"
          "  int y;\n"
          "  initial begin\n"
          "    static p::C c = new;\n"
          "    y = " +
          read +
          " * 10 + g;\n"
          "  end\n"
          "endmodule\n",
      "y");
}

TEST(PackageDeclarationSim,
     PackageClassStaticInitializerReadsPackageVariableBesideModulesOwn) {
  EXPECT_EQ(
      PackageClassReadBesideTheTopsG("    static int s = g;\n", "p::C::s"),
      57u);
}

TEST(PackageDeclarationSim,
     PackageClassPropertyInitializerReadsPackageVariableBesideModulesOwn) {
  EXPECT_EQ(PackageClassReadBesideTheTopsG("    int v = g;\n", "c.v"), 57u);
}

TEST(PackageDeclarationSim, PackageSyncVariableBuiltByItsDeclarationIsNotNull) {
  EXPECT_EQ(
      RunAndGet("package p;\n"
                "  class C;\n"
                "  endclass\n"
                "  mailbox built = new;\n"
                "  mailbox bare;\n"
                "  semaphore s = new(1);\n"
                "  C h;\n"
                "endpackage\n"
                "module top;\n"
                "  int y;\n"
                "  initial y = (p::built != null) + 10 * (p::bare == null) +\n"
                "              100 * (p::s != null) + 1000 * (p::h == null);\n"
                "endmodule\n",
                "y"),
      1111u);
}

TEST(PackageDeclarationSim, VariableOfThePackagesOwnTypedefHasItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef struct packed { bit [2:0] x; } ps_t;\n"
                       "  typedef byte sb_t;\n"
                       "  typedef string str_t;\n"
                       "  ps_t pp;\n"
                       "  sb_t sb;\n"
                       "  str_t s = \"hi\";\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    p::pp = 7'h7f; p::sb = 200;\n"
                       "    $display(\"%0d %0d %0d %0d %0d\", $bits(p::pp), "
                       "p::pp, p::sb,\n"
                       "             $bits(p::sb), p::s.len());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 7 -56 8 2\n");
}

TEST(PackageDeclarationSim, InitializerIsConvertedToTheVariablesType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  byte b = -1;\n"
                       "  shortint si = 70000;\n"
                       "  int i = 3.7;\n"
                       "  logic [99:0] wide = '1;\n"
                       "  bit [3:0] b4 = 4'bx1x1;\n"
                       "  real r = 2.5;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    $display(\"%0d %0d %0d %0d %0d %b %0d %f\", "
                       "$bits(p::b), p::b, p::si,\n"
                       "             p::i, $bits(p::wide), p::b4, &p::wide, "
                       "p::r);\n"
                       "    p::b = 200;\n"
                       "    $display(\"%0d\", p::b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "8 -1 4464 4 100 0101 1 2.500000\n-56\n");
}

}  // namespace
