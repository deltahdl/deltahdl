#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(PackageExportSim, FunctionVisibleThroughExplicitReExport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  function automatic int get_val();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::get_val;\n"
      "  export p1::get_val;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::get_val;\n"
      "  int r;\n"
      "  initial r = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 42u);
}

TEST(PackageExportSim, FunctionVisibleThroughWildcardReExport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  function automatic int get_val();\n"
      "    return 7;\n"
      "  endfunction\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::*;\n"
      "  export p1::*;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::get_val;\n"
      "  int r;\n"
      "  initial r = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 7u);
}

TEST(PackageExportSim, FunctionVisibleThroughStarStarExport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  function automatic int get_val();\n"
      "    return 99;\n"
      "  endfunction\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::*;\n"
      "  export *::*;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::get_val;\n"
      "  int r;\n"
      "  initial r = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 99u);
}

TEST(PackageExportSim, FunctionVisibleThroughReExportChain) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  function automatic int get_val();\n"
      "    return 13;\n"
      "  endfunction\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::get_val;\n"
      "  export p1::get_val;\n"
      "endpackage\n"
      "package p3;\n"
      "  import p2::get_val;\n"
      "  export p2::get_val;\n"
      "endpackage\n"
      "module t;\n"
      "  import p3::get_val;\n"
      "  int r;\n"
      "  initial r = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 13u);
}

TEST(PackageExportSim, MultipleFunctionsExportedViaStarStarResolve) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  function automatic int first();\n"
      "    return 11;\n"
      "  endfunction\n"
      "  function automatic int second();\n"
      "    return 22;\n"
      "  endfunction\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::*;\n"
      "  export *::*;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::*;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = first();\n"
      "    b = second();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 11u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 22u);
}

TEST(PackageExportSim, WildcardExportConsumedByWildcardImport) {
  // A wildcard export (p1::*) is consumed by a wildcard import of the
  // re-exporting package, so resolution flows through the all-imported lowering
  // path rather than the single-name path.
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  function automatic int get_val();\n"
      "    return 55;\n"
      "  endfunction\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::*;\n"
      "  export p1::*;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::*;\n"
      "  int r;\n"
      "  initial r = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 55u);
}

TEST(PackageExportSim, SpecificExportConsumedByWildcardImport) {
  // A specific export (p1::get_val) is consumed by a wildcard import of the
  // re-exporting package; the all-imported lowering path follows the specific
  // export back to its original declaration.
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  function automatic int get_val();\n"
      "    return 66;\n"
      "  endfunction\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::get_val;\n"
      "  export p1::get_val;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::*;\n"
      "  int r;\n"
      "  initial r = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 66u);
}

TEST(PackageExportSim, WildcardImportedNameSpecificallyExportedIsUsable) {
  // §26.6: a name made available to the exporting package through a wildcard
  // import (never otherwise referenced) may still be named in a specific
  // export; the export brings it in following the same rules as a direct
  // import, so a downstream consumer resolves it to the original declaration
  // and runs it. This is the wildcard-source + specific-export composition,
  // distinct from the explicit-import and wildcard-export sim cases.
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  function automatic int get_val();\n"
      "    return 77;\n"
      "  endfunction\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::*;\n"
      "  export p1::get_val;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::get_val;\n"
      "  int r;\n"
      "  initial r = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 77u);
}

TEST(PackageExportSim, LocalparamValueSpecificallyReExported) {
  // §26.6: an `export pkg::name` makes the declaration available downstream for
  // any declaration kind, not only subroutines. A re-exported localparam's
  // value must resolve through the export chain back to the package that
  // declares it, so the consumer reads the original constant.
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  localparam int k = 21;\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::k;\n"
      "  export p1::k;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::k;\n"
      "  int r;\n"
      "  initial r = k;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 21u);
}

TEST(PackageExportSim, VariableValueReExportedThroughWildcards) {
  // §26.6: a package variable made visible through a wildcard import and then a
  // wildcard export is available to a wildcard-importing consumer. This drives
  // the all-imported lowering path for a data declaration rather than a
  // subroutine, and observes the original variable's initialized value.
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  int g = 30;\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::*;\n"
      "  export p1::*;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::*;\n"
      "  int r;\n"
      "  initial r = g;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 30u);
}

TEST(PackageExportSim, MultipleExportedPathsToSameDeclarationDoNotConflict) {
  // §26.6: an import of a declaration made visible through an export is
  // equivalent to an import of the original declaration, so reaching the same
  // p1::get_val through two independent re-exporting packages (p2 and p4),
  // both wildcard-imported here, resolves without conflict.
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  function automatic int get_val();\n"
      "    return 88;\n"
      "  endfunction\n"
      "endpackage\n"
      "package p2;\n"
      "  import p1::get_val;\n"
      "  export p1::get_val;\n"
      "endpackage\n"
      "package p4;\n"
      "  import p1::get_val;\n"
      "  export p1::get_val;\n"
      "endpackage\n"
      "module t;\n"
      "  import p2::*;\n"
      "  import p4::*;\n"
      "  int r;\n"
      "  initial r = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 88u);
}

}  // namespace
