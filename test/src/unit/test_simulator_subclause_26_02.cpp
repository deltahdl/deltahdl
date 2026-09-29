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
      "    static p::Helper h = new;\n"
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
      "    static p::Helper h = new;\n"
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
      "    static p::C c = new;\n"
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
      "    static p::Holder h = new;\n"
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
      "    static User u = new;\n"
      "    r = u.run(); k = u.k();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"r", 50u}, {"k", 17u}});
}

// A design whose package p declares `int g = 5;` and then the class C of
// `class_body`, and whose top declares its own `int g = 7;`, constructs a
// `p::C` and reads `read * 10 + g` into y; answers y, in which the tens
// digit is what the class read and the units the top's own g.
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

// §26.2 (printed page 808) with §8.9 (printed 186): the package class's
// `static int s = g;` is an expression of the package's scope, whose g is 5,
// initialized once, so `p::C::s * 10 + g` in a top declaring its own `int g
// = 7` is 57. Passes since a544a27b7, which lowers a class inside a frame of
// its declaring scope; the initializer was evaluated in no frame before,
// resolving g through no key: s read 0 and y 7.
TEST(PackageDeclarationSim,
     PackageClassStaticInitializerReadsPackageVariableBesideModulesOwn) {
  EXPECT_EQ(
      PackageClassReadBesideTheTopsG("    static int s = g;\n", "p::C::s"),
      57u);
}

// §26.2 (printed page 808) with §8.7 (printed 184) and §23.9 (printed 761):
// the package class's `int v = g;` default is read in the class's declaring
// scope as the object is constructed, never in the constructing module's,
// so `c.v * 10 + g` beside the top's own g is 57; a default resolving g
// through the top's instance read 7: 77.
TEST(PackageDeclarationSim,
     PackageClassPropertyInitializerReadsPackageVariableBesideModulesOwn) {
  EXPECT_EQ(PackageClassReadBesideTheTopsG("    int v = g;\n", "c.v"), 57u);
}

// §26.2 (printed page 808) with §8.4 (printed pages 181-182), §15.4.1
// (printed 374) and §15.3.1 (printed 373): a package's variable declaration
// assignments complete before any initial procedure starts, and a mailbox's
// or a semaphore's is the new() that returns the handle its variable holds,
// so `p::built` and `p::s` refer to the queue and the bucket when the
// module reads them while `p::bare` and `p::h`, declared with no
// initializer, hold the null handle §8.4's Table 8-1 gives a handle by
// default. `p::built != null` adds 1, `p::bare == null` 10, `p::s != null`
// 100 and `p::h == null` 1000: 1111. The package's new() sized the queue
// and filled the bucket and left the variable's value at the 0 its storage
// was created with, so built and s read as null; and a package's handle
// with no initializer was shaped as a 4-state named type and filled with
// x, so `p::bare == null` and `p::h == null` read x, the sum x and y 0.
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

// §26.2 with §6.18: a package's variable written with a typedef the package
// itself declares has the type that typedef stands for -- a three-bit packed
// structure three bits wide, keeping 7 of 7'h7f, a byte typedef signed, a
// string typedef a string. Looked up by its bare name, the typedef was
// found nowhere: the structure was 32 bits and kept 127, the byte read 200
// for 200, and the string's len() answered 0.
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

// §26.2 with §6.8 and §10.7: a package variable's initializer is assigned to
// it, so the value takes the variable's type -- a byte's eight bits, a
// shortint's sixteen, a real rounded into an int, an unbased unsized literal
// filling the width, a bit's x bits made 0. Stored as it evaluated, `byte b =
// -1` held 32 bits and then kept 200 for 200, `int i = 3.7` read 3, and `'1`
// made a one-bit vector.
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
