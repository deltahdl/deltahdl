#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- Requirement 1: :: prefix resolves downward ---

TEST(ScopeResolutionPrefixSim, PackagePrefixResolvesDownward) {
  EXPECT_EQ(RunAndGet(
      "package pkg;\n"
      "  parameter int VAL = 42;\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = pkg::VAL;\n"
      "endmodule\n", "result"), 42u);
}

TEST(ScopeResolutionPrefixSim, ClassPrefixResolvesDownward) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  static int val = 77;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = C::val;\n"
      "endmodule\n", "result"), 77u);
}

// --- Requirement 2: :: prefix never uses upward resolution ---

TEST(ScopeResolutionPrefixSim, PrefixDoesNotResolveToLocalVariable) {
  EXPECT_EQ(RunAndGet(
      "class Base;\n"
      "  static int x = 10;\n"
      "endclass\n"
      "module t;\n"
      "  int x = 999;\n"
      "  int result;\n"
      "  initial result = Base::x;\n"
      "endmodule\n", "result"), 10u);
}

TEST(ScopeResolutionPrefixSim, PackagePrefixDoesNotResolveToLocalVariable) {
  EXPECT_EQ(RunAndGet(
      "package pkg;\n"
      "  parameter int N = 5;\n"
      "endpackage\n"
      "module t;\n"
      "  int N = 999;\n"
      "  int result;\n"
      "  initial result = pkg::N;\n"
      "endmodule\n", "result"), 5u);
}

// --- Requirement 3: class vs. package disambiguation ---

TEST(ScopeResolutionPrefixSim, VisibleClassNameDenotesClassScope) {
  EXPECT_EQ(RunAndGet(
      "class Cfg;\n"
      "  static int WIDTH = 8;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = Cfg::WIDTH;\n"
      "endmodule\n", "result"), 8u);
}

TEST(ScopeResolutionPrefixSim, UnresolvablePrefixDenotesPackageScope) {
  EXPECT_EQ(RunAndGet(
      "package nums;\n"
      "  parameter int MAX = 255;\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = nums::MAX;\n"
      "endmodule\n", "result"), 255u);
}

TEST(ScopeResolutionPrefixSim, ClassAndPackagePrefixesResolveIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int A = 11;\n"
      "endpackage\n"
      "class Cls;\n"
      "  static int B = 22;\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = pkg::A;\n"
      "    r2 = Cls::B;\n"
      "  end\n"
      "endmodule\n", f);
  LowerRunAndCheck(f, design, {{"r1", 11u}, {"r2", 22u}});
}

}  // namespace
