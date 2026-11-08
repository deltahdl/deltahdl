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

TEST(PackageExportSim, ExportedInitializedFixedSizeArrayReadThroughExporter) {
  EXPECT_EQ(ExportedArrayRead("module top;\n"
                              "  int y;\n"
                              "  initial y = q::a[1] * 10 + q::a[0];\n"
                              "endmodule\n"),
            21u);
}

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
