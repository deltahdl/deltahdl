#include "fixture_simulator.h"

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

TEST(PackageImportSim, QualifiedRefUsesPackageNotExplicitImport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int VAL = 10;\n"
      "endpackage\n"
      "package q;\n"
      "  parameter int VAL = 20;\n"
      "endpackage\n"
      "module t;\n"
      "  import q::VAL;\n"
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

}  // namespace
