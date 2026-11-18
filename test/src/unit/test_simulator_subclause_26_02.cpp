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

TEST(PackageDeclarationSim, EveryAlwaysKindReadsThePackageInitializerFirst) {
  for (const char* procedure :
       {"  always @(posedge clk) $display(\"%0d\", g);\n",
        "  always_ff @(posedge clk) $display(\"%0d\", g);\n",
        "  always_latch $display(\"%0d\", g);\n",
        "  always_comb $display(\"%0d\", g);\n"}) {
    const std::string kSrc = std::string(
                                 "package p; int g = 3; endpackage\n"
                                 "module t;\n"
                                 "  import p::*;\n"
                                 "  logic clk = 0;\n"
                                 "  initial clk = 1;\n") +
                             procedure + "endmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(kSrc, f), "3\n") << kSrc;
    EXPECT_FALSE(f.diag.HasErrors()) << kSrc;
  }
}

TEST(PackageDeclarationSim, ScopedReadOfAPackageInitializerAtTimeZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p; int g = 3; endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%0d\", p::g);\n"
                       "endmodule\n",
                       f),
            "3\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackageDeclarationSim,
     DISABLED_TheSectionsComplexPackageAddsAndMultiplies) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package ComplexPkg;\n"
                 "  typedef struct {\n"
                 "    shortreal i, r;\n"
                 "  } Complex;\n"
                 "  function Complex add(Complex a, b);\n"
                 "    add.r = a.r + b.r;\n"
                 "    add.i = a.i + b.i;\n"
                 "  endfunction\n"
                 "  function Complex mul(Complex a, b);\n"
                 "    mul.r = (a.r * b.r) - (a.i * b.i);\n"
                 "    mul.i = (a.r * b.i) + (a.i * b.r);\n"
                 "  endfunction\n"
                 "endpackage : ComplexPkg\n"
                 "module top;\n"
                 "  ComplexPkg::Complex a = '{1.0, 2.0}, b = '{3.0, 4.0};\n"
                 "  ComplexPkg::Complex s, m;\n"
                 "  initial begin\n"
                 "    s = ComplexPkg::add(a, b);\n"
                 "    m = ComplexPkg::mul(a, b);\n"
                 "    $display(\"%0.1f %0.1f %0.1f %0.1f\", s.i, s.r, m.i, "
                 "m.r);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "4.0 6.0 10.0 5.0\n");
}

TEST(PackageDeclarationSim, ACheckersClockedProcessesRunInItsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(
                ElaborateSrc,
                "package p;\n"
                "  checker ck(logic clk, logic v);\n"
                "    int n = 0;\n"
                "    initial @(posedge clk) assert (v) $display(\"init ok\");\n"
                "      else $display(\"init bad\");\n"
                "    always_ff @(posedge clk) n <= n + 1;\n"
                "    final $display(\"final n=%0d\", n);\n"
                "  endchecker\n"
                "endpackage\n"
                "module top;\n"
                "  logic clk = 0, v = 1;\n"
                "  initial repeat (6) #5 clk = ~clk;\n"
                "  p::ck c(clk, v);\n"
                "endmodule\n",
                f),
            "init ok\nfinal n=3\n");
}

TEST(PackageDeclarationSim, ACheckersCombinationalProcessesRunInItsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "package p;\n"
                                    "  checker ck(logic a);\n"
                                    "    logic b, l;\n"
                                    "    always_comb b = !a;\n"
                                    "    always_latch if (a) l = !a;\n"
                                    "    final $display(\"b=%b l=%b\", b, l);\n"
                                    "  endchecker\n"
                                    "endpackage\n"
                                    "module top;\n"
                                    "  logic a = 1;\n"
                                    "  p::ck c(a);\n"
                                    "endmodule\n",
                                    f),
            "b=0 l=0\n");
}

std::string RunPackageNet(const std::string& package_items,
                          const std::string& modules) {
  SimFixture f;
  return RunCapture("package p;\n" + package_items + "endpackage\n" + modules,
                    f);
}

constexpr const char* kByteNet = "  wire [7:0] w;\n";

TEST(PackageDeclarationSim, DISABLED_AWildcardImportedNetIsDriven) {
  EXPECT_EQ(RunPackageNet(kByteNet,
                          "module top;\n"
                          "  import p::*;\n"
                          "  assign w = 8'hA5;\n"
                          "  initial #1 $display(\"%h %0d\", w, $bits(w));\n"
                          "endmodule\n"),
            "a5 8\n");
}

TEST(PackageDeclarationSim, DISABLED_AScopedNetIsDriven) {
  EXPECT_EQ(RunPackageNet(kByteNet,
                          "module top;\n"
                          "  assign p::w = 8'hA5;\n"
                          "  initial #1 $display(\"%h\", p::w);\n"
                          "endmodule\n"),
            "a5\n");
}

TEST(PackageDeclarationSim, DISABLED_AnExplicitlyImportedNetIsDriven) {
  EXPECT_EQ(RunPackageNet(kByteNet,
                          "module top;\n"
                          "  import p::w;\n"
                          "  assign w = 8'hA5;\n"
                          "  initial #1 $display(\"%h\", w);\n"
                          "endmodule\n"),
            "a5\n");
}

TEST(PackageDeclarationSim, AWandNetResolvesTheDriversOfTwoInstances) {
  EXPECT_EQ(RunPackageNet("  wand w;\n",
                          "module d #(parameter bit V = 0);\n"
                          "  assign p::w = V;\n"
                          "endmodule\n"
                          "module top;\n"
                          "  d #(1) d1();\n"
                          "  d #(0) d0();\n"
                          "  initial #1 $display(\"%b\", p::w);\n"
                          "endmodule\n"),
            "0\n");
}

TEST(PackageDeclarationSim, DISABLED_AnUndrivenTri1NetPullsUp) {
  EXPECT_EQ(RunPackageNet("  tri1 w;\n",
                          "module top;\n"
                          "  initial #1 $display(\"%b\", p::w);\n"
                          "endmodule\n"),
            "1\n");
}

TEST(PackageDeclarationSim, DISABLED_ALocalNetHidesTheWildcardImportedOne) {
  EXPECT_EQ(RunPackageNet("  wire w;\n",
                          "module top;\n"
                          "  import p::*;\n"
                          "  wire w;\n"
                          "  assign w = 1;\n"
                          "  initial #1 $display(\"%b %b\", w, p::w);\n"
                          "endmodule\n"),
            "1 z\n");
}

TEST(PackageDeclarationSim, DISABLED_ANettypeNetResolvesByItsFunction) {
  EXPECT_EQ(
      RunPackageNet("  function automatic logic [3:0] rs(input logic [3:0] "
                    "d[]);\n"
                    "    rs = 0;\n"
                    "    foreach (d[i]) rs |= d[i];\n"
                    "  endfunction\n"
                    "  nettype logic [3:0] n4 with rs;\n"
                    "  n4 w;\n",
                    "module d #(parameter logic [3:0] V = 0);\n"
                    "  assign p::w = V;\n"
                    "endmodule\n"
                    "module top;\n"
                    "  d #(4'b0011) a();\n"
                    "  d #(4'b1000) b();\n"
                    "  initial #1 $display(\"%b\", p::w);\n"
                    "endmodule\n"),
      "1011\n");
}

}  // namespace
