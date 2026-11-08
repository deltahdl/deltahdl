#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackageImportSim,
     WildcardImportReachesAProcessInsideAConditionalGenerateBlock) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x;\n"
                      "  int k = 7;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y, z;\n"
                      "  if (1) begin : b\n"
                      "    initial x = 1;\n"
                      "    initial y = 4;\n"
                      "    initial #1 z = x * 10 + k;\n"
                      "  end\n"
                      "  initial #2 y = y * 1000 + p::x * 100 + z;\n"
                      "endmodule\n",
                      "y"),
            4117u);
}

TEST(PackageImportSim, WildcardImportReachesEachLoopGenerateBlockInstance) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y;\n"
                      "  genvar g;\n"
                      "  for (g = 0; g < 3; g++) begin : blk\n"
                      "    initial x = x + (g + 1) * 10;\n"
                      "  end\n"
                      "  initial #1 y = p::x;\n"
                      "endmodule\n",
                      "y"),
            60u);
}

TEST(PackageImportSim, ChildInstanceImportReachesItsOwnGenerateBlocks) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "module c;\n"
                      "  import p::*;\n"
                      "  int seen;\n"
                      "  if (1) begin : b\n"
                      "    initial x = 5;\n"
                      "    initial #2 seen = x;\n"
                      "  end\n"
                      "  genvar g;\n"
                      "  for (g = 0; g < 2; g++) begin : blk\n"
                      "    initial #1 x = x + g + 1;\n"
                      "  end\n"
                      "endmodule\n"
                      "module top;\n"
                      "  c u1();\n"
                      "  int y;\n"
                      "  initial #3 y = p::x * 100 + u1.seen;\n"
                      "endmodule\n",
                      "y"),
            808u);
}

TEST(PackageImportSim,
     GenerateBlockDeclarationShadowsTheModulesWildcardImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x = 3;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int out, y;\n"
                      "  if (1) begin : b\n"
                      "    int x;\n"
                      "    initial begin\n"
                      "      x = 9;\n"
                      "      out = x;\n"
                      "    end\n"
                      "  end\n"
                      "  initial #1 y = p::x * 10 + out;\n"
                      "endmodule\n",
                      "y"),
            39u);
}

TEST(PackageImportSim, CalleeWithoutImportKeepsTheModulesFunctionOverCallers) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int plain(); return five(); endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return five() * 100 + plain();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            550u);
}

TEST(PackageImportSim, CalleeWithoutImportKeepsTheModulesVariableOverCallers) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int v = 3;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int v = 40;\n"
                      "  function int plain(); return v; endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return v * 100 + plain();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            340u);
}

TEST(PackageImportSim, EnabledTaskWithoutImportKeepsTheModulesFunction) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  task t_plain(output int r); r = five(); endtask\n"
                      "  task t_calc(output int r);\n"
                      "    import p::*;\n"
                      "    int q;\n"
                      "    t_plain(q);\n"
                      "    r = five() * 100 + q;\n"
                      "  endtask\n"
                      "  int out;\n"
                      "  initial t_calc(out);\n"
                      "endmodule\n",
                      "out"),
            550u);
}

TEST(PackageImportSim, ClassMethodWithoutImportKeepsTheModulesFunction) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  class C;\n"
                      "    function int get(); return five(); endfunction\n"
                      "  endclass\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    static C c = new;\n"
                      "    return five() * 100 + c.get();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            550u);
}

TEST(PackageImportSim, PropertyDefaultKeepsTheModulesFunctionOverConstructors) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  class C;\n"
                      "    int x = five();\n"
                      "  endclass\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    static C c = new;\n"
                      "    return five() * 100 + c.x;\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            550u);
}

TEST(PackageImportSim,
     PackageClassPropertyDefaultReadsItsPackageFromAModuleBody) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "  class C;\n"
                      "    int x = five();\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int calc();\n"
                      "    static p::C c = new;\n"
                      "    return five() * 100 + c.x;\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            5005u);
}

TEST(PackageImportSim,
     SpecializedClassPropertyDefaultReadsItsParameterInAnImportingBody) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int W = 3;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  class C #(int W = 1);\n"
                      "    int x = W;\n"
                      "  endclass\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    C c;\n"
                      "    c = C#(7)::new;\n"
                      "    return c.x * 100 + five();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            705u);
}

TEST(PackageImportSim, BlockAndForeachInsideAnImportingBodySeeItsImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  int arr[2];\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    int s;\n"
                      "    s = 0;\n"
                      "    begin : blk\n"
                      "      s = s + five();\n"
                      "    end\n"
                      "    foreach (arr[i]) s = s + five();\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            15u);
}

TEST(PackageScopeReferenceSim,
     PackageFunctionCalledFromAModuleBodyStillReadsItsPackage) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "  function int ten(); return five() * 2; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int plain(); return p::ten() + five(); "
                      "endfunction\n"
                      "  int out;\n"
                      "  initial out = plain();\n"
                      "endmodule\n",
                      "out"),
            60u);
}

TEST(PackageImportSim, BlockImportAfterTheReferenceLeavesItToTheOuterScope) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  int x = 7;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y, z;\n"
                      "  if (1) begin : b\n"
                      "    initial x = 1;\n"
                      "    import p2::*;\n"
                      "    initial #1 z = x;\n"
                      "  end\n"
                      "  initial #2 y = p::x * 1000 + x * 100 + z;\n"
                      "endmodule\n",
                      "y"),
            1107u);
}

TEST(PackageImportSim, SiblingBlocksEachReadTheirOwnImport) {
  EXPECT_EQ(RunAndGet("package p2;\n"
                      "  int x = 5;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  int x = 9;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y, seen_b, seen_c;\n"
                      "  if (1) begin : b\n"
                      "    import p2::*;\n"
                      "    initial seen_b = x;\n"
                      "  end\n"
                      "  if (1) begin : c\n"
                      "    import p3::*;\n"
                      "    initial seen_c = x;\n"
                      "  end\n"
                      "  initial #1 y = seen_b * 100 + seen_c;\n"
                      "endmodule\n",
                      "y"),
            509u);
}

TEST(PackageImportSim, NestedBlockReachesTheEnclosingBlocksImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x = 3;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  int x = 5;\n"
                      "  int k = 2;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y, inner, own;\n"
                      "  if (1) begin : b\n"
                      "    import p2::*;\n"
                      "    int k = 40;\n"
                      "    if (1) begin : c\n"
                      "      initial inner = x + k;\n"
                      "    end\n"
                      "    initial own = k;\n"
                      "  end\n"
                      "  initial #1 y = inner * 100 + own;\n"
                      "endmodule\n",
                      "y"),
            4540u);
}

TEST(PackageImportSim, LoopBlockInstanceImportBindsAfterItsPoint) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x = 1;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  int x = 10;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y;\n"
                      "  genvar g;\n"
                      "  for (g = 0; g < 2; g++) begin : blk\n"
                      "    initial y = y + x;\n"
                      "    import p2::*;\n"
                      "    initial #1 y = y + x;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            22u);
}

TEST(PackageImportSim, TwoExplicitImportsThroughTwoExportsBindOneVariable) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export p1::x;\n"
                      "endpackage\n"
                      "package p4;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int seen = x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::x;\n"
                      "  import p4::x;\n"
                      "  int y;\n"
                      "  initial x = 37;\n"
                      "  initial #1 y = x * 100 + p1::x;\n"
                      "endmodule\n",
                      "y"),
            3737u);
}

TEST(PackageImportSim, ReExportedNameThroughTheExportingPackageQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export p1::x;\n"
                      "endpackage\n"
                      "package p4;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int seen = x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  int y;\n"
                      "  initial p2::x = 37;\n"
                      "  initial #1 y = p1::x * 10000 + p4::x * 100 + x;\n"
                      "endmodule\n",
                      "y"),
            373737u);
}

TEST(PackageImportSim, ReExportedFunctionCalledThroughTheExportingPackage) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int k = 4;\n"
                      "  function automatic int f();\n"
                      "    return k * 10 + 1;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::f;\n"
                      "  export p1::f;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::f();\n"
                      "endmodule\n",
                      "y"),
            41u);
}

TEST(PackageImportSim, ReExportChainWrittenThroughTheLastPackage) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int seen = x;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::x;\n"
                      "  export *::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial p3::x = 5;\n"
                      "  initial #1 y = p2::x * 10 + p1::x;\n"
                      "endmodule\n",
                      "y"),
            55u);
}

TEST(PackageImportSim,
     WildcardReExportedLiteralAndParameterThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {LOW, MID = 6, HIGH} level_t;\n"
                      "  parameter int K = 3;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int seen = MID + K;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::MID * 10 + p2::K;\n"
                      "endmodule\n",
                      "y"),
            63u);
}

TEST(PackageImportSim, ReExportedClassThroughTheExportingPackageQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    static function int get(); return 7; endfunction\n"
                      "    int v = 3;\n"
                      "  endclass\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::C;\n"
                      "  export p1::C;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static p2::C h = new;\n"
                      "    y = p2::C::get() * 100 + h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            703u);
}

TEST(PackageImportSim, ReExportedClassAlongAWildcardExportChain) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    static function int get(); return 7; endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  typedef C seen_t;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::C;\n"
                      "  export p2::C;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::C::get() * 10 + p3::C::get();\n"
                      "endmodule\n",
                      "y"),
            77u);
}

TEST(PackageImportSim, ReExportedClassReachedBareThroughAWildcardImport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    static function int get(); return 7; endfunction\n"
                      "    int v = 3;\n"
                      "  endclass\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  typedef C seen_t;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C h = new;\n"
                      "    y = h.v * 100 + C::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            307u);
}

TEST(PackageImportSim, ReExportedClassHandleConstructedThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::h;\n"
                      "  export p1::h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p2::h = new;\n"
                      "    p2::h.v = 5;\n"
                      "    y = p1::h.v * 10 + p2::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            55u);
}

TEST(PackageImportSim, ReExportedStringWrittenAndReadThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  string s;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::s;\n"
                      "  export p1::s;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p2::s = \"abcd\";\n"
                      "    y = p2::s.len() * 10 + p1::s.len();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            44u);
}

TEST(PackageImportSim,
     PackageFunctionWritesItsOwnQueueAndAssociativeArrayBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$];\n"
                      "  int m[string];\n"
                      "  function void add(int v);\n"
                      "    q.push_back(v);\n"
                      "    m[\"k\"] = v;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::add(5);\n"
                      "    y = p1::q.size() * 10 + p1::m[\"k\"];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            15u);
}

TEST(PackageImportSim, PackageFunctionWritesAnImportedPackagesQueueBare) {
  EXPECT_EQ(RunAndGet("package p0;\n"
                      "  int r[$];\n"
                      "endpackage\n"
                      "package p1;\n"
                      "  import p0::*;\n"
                      "  function void addr(int v);\n"
                      "    r.push_back(v);\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::addr(3);\n"
                      "    p1::addr(4);\n"
                      "    y = p0::r.size() * 10 + p0::r[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            24u);
}

TEST(PackageImportSim,
     PackageFixedSizeArrayElementWrittenAndReadThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::a[1] = 7;\n"
                      "    y = p1::a[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            7u);
}

TEST(PackageImportSim,
     PackageDynamicArrayElementWrittenAndReadThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int d[];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::d = new[3];\n"
                      "    p1::d[2] = 5;\n"
                      "    y = p1::d[2];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            5u);
}

TEST(PackageImportSim,
     PackageFixedSizeArrayElementCompoundAssignedThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::a[1] = 7;\n"
                      "    p1::a[1] += 2;\n"
                      "    y = p1::a[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            9u);
}

TEST(PackageImportSim,
     PackageQueueElementReadThroughTheQualifierBesideAnArray) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$];\n"
                      "  int a[2];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::q.push_back(4);\n"
                      "    p1::a[1] = 3;\n"
                      "    y = p1::q[0] * 10 + p1::a[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            43u);
}

}  // namespace
