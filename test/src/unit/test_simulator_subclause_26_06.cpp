#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

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
      "  function automatic int seen(); return get_val(); endfunction\n"
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
      "  function automatic int seen(); return get_val(); endfunction\n"
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
      "  function automatic int seen(); return first() + second(); "
      "endfunction\n"
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
      "  function automatic int seen(); return get_val(); endfunction\n"
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
      "  int seen = g;\n"
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

// A design whose package p declares `int a[2] = '{1, 2};` and a function f
// reading a[0], and whose package q imports p, reads a, which imports it, and
// exports p's names, ahead of the module `top`, whose process reads into y;
// answers y.
static uint64_t ExportedArrayRead(const std::string& top) {
  return RunAndGet(
      "package p;\n"
      "  int a[2] = '{1, 2};\n"
      "  function int f();\n"
      "    return a[0];\n"
      "  endfunction\n"
      "endpackage\n"
      "package q;\n"
      "  import p::*;\n"
      "  export p::*;\n"
      "  int seen = a[0];\n"
      "endpackage\n" +
          top,
      "y");
}

// §26.6 (printed pages 815-816) with §7.4.2 (printed 154) and §26.2
// (printed 808): q's `export p::*` hands p's array on, so `q::a[1]` and
// `q::a[0]` through the exporter's qualifier are the elements p's
// declaration assignment `'{1, 2}` gave their values: 2 * 10 + 1. The
// export bound the elements as they stood at creation, at their defaults,
// and p's initializer then remade the elements under p's keys
// (InitPackageArray in lowerer_package_data.cpp), so the exporter's keys
// held the stale elements and both read 0. The initializer is now written
// into the elements the export bound (InitArrayElements, lowerer_var.cpp).
TEST(PackageExportSim, ExportedInitializedFixedSizeArrayReadThroughExporter) {
  EXPECT_EQ(ExportedArrayRead("module top;\n"
                              "  int y;\n"
                              "  initial y = q::a[1] * 10 + q::a[0];\n"
                              "endmodule\n"),
            21u);
}

// §26.6: p's a and q's a are one declaration, so `q::a[0] = 9` through the
// exporter is the element p's own f() reads: 9. A write landing on a stale
// element the export bound left p's element at its initializer's 1.
TEST(PackageExportSim, WriteThroughExporterReachesTheDeclaringPackagesElement) {
  EXPECT_EQ(ExportedArrayRead("module top;\n"
                              "  int y;\n"
                              "  initial begin\n"
                              "    q::a[0] = 9;\n"
                              "    y = p::f();\n"
                              "  end\n"
                              "endmodule\n"),
            9u);
}

// §26.6 (printed page 815): `export p1::*` hands on only what p2 imported from
// p1, the x of `import p1::x`, so p7's y is the one top's wildcard import of p7
// reaches, and p0's w, which p2 imports but exports nothing of, is handed on by
// neither. The export handed on the whole of p1, so p1's y took the name first
// and top read 10.
TEST(PackageExportSim, WildcardExportHandsOnOnlyTheExplicitImport) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p1; int x = 1; int y = 10; endpackage\n"
                       "package p0; int w = 4; endpackage\n"
                       "package p2;\n"
                       "  import p0::w;\n"
                       "  import p1::x;\n"
                       "  export p1::*;\n"
                       "endpackage\n"
                       "package p7; int y = 70; endpackage\n"
                       "module top;\n"
                       "  import p2::*;\n"
                       "  import p7::*;\n"
                       "  initial $display(\"x=%0d y=%0d\", x, y);\n"
                       "endmodule\n",
                       f),
            "x=1 y=70\n");
}

// The same for `export *::*`: p8 imports p7's y alone, so p9's z is the one top
// reads. The export handed on the whole of p7, and top read p7's 70.
TEST(PackageExportSim, StarExportHandsOnOnlyTheExplicitImport) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p7; int y = 1; int z = 70; endpackage\n"
                       "package p8;\n"
                       "  export *::*;\n"
                       "  import p7::y;\n"
                       "endpackage\n"
                       "package p9; int z = 90; endpackage\n"
                       "module top;\n"
                       "  import p8::*;\n"
                       "  import p9::*;\n"
                       "  initial $display(\"y=%0d z=%0d\", y, z);\n"
                       "endmodule\n",
                       f),
            "y=1 z=90\n");
}

// §26.6 (printed page 815) with §26.3 (printed 810): p4's wildcard import of
// p1 imports the x p4 reads and not the y it never references, so `export
// p1::*` hands on x alone and p7's y is the one top reads. The export handed
// on every candidate of p1, and top read p1's 10.
TEST(PackageExportSim, WildcardExportHandsOnOnlyReferencedCandidates) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p1; int x = 1; int y = 10; endpackage\n"
                       "package p4;\n"
                       "  import p1::*;\n"
                       "  export p1::*;\n"
                       "  int q = x;\n"
                       "endpackage\n"
                       "package p7; int y = 70; endpackage\n"
                       "module top;\n"
                       "  import p4::*;\n"
                       "  import p7::*;\n"
                       "  initial $display(\"x=%0d y=%0d\", x, y);\n"
                       "endmodule\n",
                       f),
            "x=1 y=70\n");
}

// The same for `export *::*`: p4 calls p1's f and never names p1's y, so f is
// handed on and p7's y is the one top reads.
TEST(PackageExportSim, StarExportHandsOnOnlyReferencedCandidates) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p1;\n"
                       "  int y = 10;\n"
                       "  function int f(); return 5; endfunction\n"
                       "endpackage\n"
                       "package p4;\n"
                       "  import p1::*;\n"
                       "  export *::*;\n"
                       "  int q = f();\n"
                       "endpackage\n"
                       "package p7; int y = 70; endpackage\n"
                       "module top;\n"
                       "  import p4::*;\n"
                       "  import p7::*;\n"
                       "  initial $display(\"f=%0d y=%0d\", f(), y);\n"
                       "endmodule\n",
                       f),
            "f=5 y=70\n");
}

}  // namespace
