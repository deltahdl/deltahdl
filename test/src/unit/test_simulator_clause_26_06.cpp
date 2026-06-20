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

}  // namespace
