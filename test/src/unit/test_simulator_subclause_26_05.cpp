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

TEST(PackageImportSim, PackageConstAndLocalparamOfPackageEnumTypeHoldLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum { FALSE, TRUE } BOOL;\n"
      "  const BOOL c = TRUE;\n"
      "  localparam BOOL d = TRUE;\n"
      "  localparam int e = 1;\n"
      "  const int sum = TRUE + 2;\n"
      "endpackage\n"
      "module top;\n"
      "  import p::*;\n"
      "  int sc, sd, se, ssum, ic, id;\n"
      "  initial begin\n"
      "    sc = p::c;\n"
      "    sd = p::d;\n"
      "    se = p::e;\n"
      "    ssum = p::sum;\n"
      "    ic = c;\n"
      "    id = d;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design,
                   {{"sc", 1u},
                    {"sd", 1u},
                    {"se", 1u},
                    {"ssum", 3u},
                    {"ic", 1u},
                    {"id", 1u}});
}

TEST(PackageImportSim, PackageParameterFromImportedPackageParameterReads) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package base;\n"
      "  parameter int K = 21;\n"
      "  function int dbl(int a); return a * 2; endfunction\n"
      "endpackage\n"
      "package d1;\n"
      "  parameter int KK = base::K;\n"
      "endpackage\n"
      "package d2;\n"
      "  import base::K;\n"
      "  parameter int KK = K;\n"
      "endpackage\n"
      "package d3;\n"
      "  import base::*;\n"
      "  function int twice_k(); return dbl(K); endfunction\n"
      "  localparam int KK = K;\n"
      "endpackage\n"
      "package d4;\n"
      "  parameter int K = 4;\n"
      "  import base::*;\n"
      "  parameter int KK = K;\n"
      "endpackage\n"
      "module top;\n"
      "  int a, b, c, d;\n"
      "  initial begin\n"
      "    a = d1::KK;\n"
      "    b = d2::KK;\n"
      "    c = d3::KK;\n"
      "    d = d4::KK;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"a", 21u}, {"b", 21u}, {"c", 21u}, {"d", 4u}});
}

}  // namespace
