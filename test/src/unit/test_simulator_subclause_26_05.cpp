#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackageImportSim, ExplicitImportMakesValueVisible) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 42;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::VAL;\n"
      "  int r;\n"
      "  initial r = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 42u);
}

TEST(PackageImportSim, QualifiedRefUsesPackageNotWildcardImport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int VAL = 10;\n"
      "endpackage\n"
      "package q;\n"
      "  parameter int VAL = 20;\n"
      "endpackage\n"
      "module t;\n"
      "  import q::*;\n"
      "  int direct_ref, qualified_ref;\n"
      "  initial begin\n"
      "    direct_ref = VAL;\n"
      "    qualified_ref = p::VAL;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("direct_ref")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("qualified_ref")->value.ToUint64(), 10u);
}

TEST(PackageImportSim, ExplicitImportShadowsWildcardImport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int VAL = 10;\n"
      "endpackage\n"
      "package q;\n"
      "  parameter int VAL = 20;\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  import q::VAL;\n"
      "  int r;\n"
      "  initial r = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 20u);
}

TEST(PackageImportSim, WildcardImportResolvesValueReference) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 77;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  int r;\n"
      "  initial r = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 77u);
}

// Table 26-1 Row B, column 1: a local declaration shadows a wildcard import of
// the same name. The direct reference resolves to the local object, while a
// qualified reference still reaches the package member. The distinct values
// prove the local and the package member are separate storage (the wildcard
// import never aliased the name onto the package member).
TEST(PackageImportSim, LocalDeclShadowsWildcardImportValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 10;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  int VAL;\n"
      "  int direct_ref, qualified_ref;\n"
      "  initial begin\n"
      "    VAL = 20;\n"
      "    direct_ref = VAL;\n"
      "    qualified_ref = pkg::VAL;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("direct_ref")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("qualified_ref")->value.ToUint64(), 10u);
}

// Table 26-1 Row B on an enumeration-constant operand, observed at run time: a
// wildcard import makes a package enum's members directly visible, so an
// unqualified reference to a member resolves to that member's value. Built from
// real package + enum syntax and run end to end (enum member B == 9).
TEST(PackageImportSim, WildcardImportedEnumMemberResolvesToValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef enum int {A = 5, B = 9} e;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  int r;\n"
      "  initial r = B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 9u);
}

// §26.2: a package's declarations are visible by their bare names throughout
// the package, so a localparam initialized from an earlier parameter of the
// package holds the computed value, read through the package scope resolution
// operator and through a wildcard import alike. L is 17 doubled: 0 was what
// an initializer evaluated outside the package's frame gave, and 17 would be
// K read unscaled; M, initialized through `p::K`, stood at 34 already.
TEST(PackageImportSim, DerivedPackageLocalparamReadsThroughScopeAndImport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int K = 17;\n"
      "  localparam int L = K * 2;\n"
      "  parameter int M = p::K * 2;\n"
      "endpackage\n"
      "module top;\n"
      "  import p::*;\n"
      "  int scoped, imported, viapkg;\n"
      "  initial begin\n"
      "    scoped = p::L;\n"
      "    imported = L;\n"
      "    viapkg = M;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design,
                   {{"scoped", 34u}, {"imported", 34u}, {"viapkg", 34u}});
}

}  // namespace
