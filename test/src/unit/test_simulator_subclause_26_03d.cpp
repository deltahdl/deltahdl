#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PackageImportSim, WildcardReExportedRangedLiteralThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int seen = VAL1 + VAL2;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y = p2::VAL2 * 10 + p2::VAL1;\n"
                      "endmodule\n",
                      "y"),
            21u);
}

TEST(PackageImportSim, ExplicitlyReExportedRangedLiteralThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::VAL2;\n"
                      "  export p1::VAL1;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::VAL2 * 10 + p2::VAL1;\n"
                      "endmodule\n",
                      "y"),
            21u);
}

TEST(PackageImportSim, ReExportedStructMemberLiteralThroughAWildcardExport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef struct { enum {IDLE, BUSY} st; } s_t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int seen = BUSY;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::BUSY * 10 + p1::BUSY;\n"
                      "endmodule\n",
                      "y"),
            11u);
}

TEST(PackageImportSim, ReExportedStructMemberLiteralThroughAnExplicitExport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef struct { enum {IDLE, BUSY} st; } s_t;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::BUSY;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::BUSY * 10 + p1::BUSY;\n"
                      "endmodule\n",
                      "y"),
            11u);
}

TEST(PackageImportSim, ImportedClassHandleConstructedThroughTheBareName) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::h;\n"
                      "  import p1::C;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    h.v = 5;\n"
                      "    y = h.v * 10 + p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            55u);
}

TEST(PackageImportSim,
     WildcardImportedClassHandleConstructedThroughTheBareName) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    h = new;\n"
                      "    h.v = 5;\n"
                      "    y = h.v * 10 + p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            55u);
}

TEST(PackageImportSim, WildcardImportedPackageQueueAndAssociativeArray) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$];\n"
                      "  int m[string];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    q.push_back(4);\n"
                      "    q.push_back(6);\n"
                      "    m[\"k\"] = 5;\n"
                      "    y = q[1] * 100 + q.size() * 10 + m[\"k\"];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            625u);
}

TEST(PackageImportSim, ExplicitlyImportedPackageQueueAndAssociativeArray) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$:1];\n"
                      "  int m[string];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::q;\n"
                      "  import p1::m;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    q.push_back(4);\n"
                      "    q.push_back(6);\n"
                      "    q.push_back(8);\n"
                      "    m[\"k\"] = 5;\n"
                      "    y = q[1] * 100 + q.size() * 10 + m[\"k\"];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            625u);
}

TEST(PackageImportSim, PackageInitializerReadingWildcardReExportedNames) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "  int x = 7;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int seen = VAL2 + x;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::*;\n"
                      "  int q = VAL2 * 10 + x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p3::q;\n"
                      "endmodule\n",
                      "y"),
            27u);
}

TEST(PackageImportSim, PackageInitializerReadingAnExplicitlyImportedReExport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 7;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int seen = x;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::x;\n"
                      "  int q = x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p3::q;\n"
                      "endmodule\n",
                      "y"),
            7u);
}

TEST(PackageImportSim, PackageSemaphoreInitializedByNewThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  semaphore s = new(2);\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::s.get(1);\n"
                      "    y = p1::s.try_get(1) * 10 + p1::s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

TEST(PackageImportSim,
     PackageSemaphoreDeclaredWithoutInitializerThroughTheQualifier) {
  EXPECT_EQ(
      RunAndGet("package p1;\n"
                "  semaphore t;\n"
                "endpackage\n"
                "module top;\n"
                "  int y;\n"
                "  initial begin\n"
                "    p1::t.put(3);\n"
                "    p1::t.get(1);\n"
                "    y = p1::t.try_get(1) * 100 + p1::t.try_get(1) * 10 +\n"
                "        p1::t.try_get(1);\n"
                "  end\n"
                "endmodule\n",
                "y"),
      110u);
}

TEST(PackageImportSim, PackageFixedSizeArrayReadAndWrittenInItsOwnFunctions) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[4];\n"
                      "  function void set(int i, int v);\n"
                      "    a[i] = v;\n"
                      "  endfunction\n"
                      "  function int get(int i);\n"
                      "    return a[i];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::set(1, 7);\n"
                      "    p1::set(3, 2);\n"
                      "    y = p1::get(1) * 10 + p1::get(3);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            72u);
}

TEST(PackageImportSim, PackageFixedSizeArrayIteratedByForeachInItsOwnFunction) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[4];\n"
                      "  function void set(int i, int v);\n"
                      "    a[i] = v;\n"
                      "  endfunction\n"
                      "  function int sum();\n"
                      "    static int s = 0;\n"
                      "    foreach (a[i]) s += a[i];\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::set(1, 7);\n"
                      "    p1::set(3, 2);\n"
                      "    y = p1::sum();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            9u);
}

TEST(PackageImportSim, PackageFixedSizeArrayCountedByForeachThroughQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[4];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y = 0;\n"
                      "  initial foreach (p1::a[i]) y++;\n"
                      "endmodule\n",
                      "y"),
            4u);
}

TEST(PackageImportSim, PackageDynamicArraySizedByNewThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int d[];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::d = new[3];\n"
                      "    p1::d[2] = 9;\n"
                      "    y = p1::d.size() * 10 + p1::d[2];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            39u);
}

TEST(PackageImportSim, PackageQueueInitializedByAnAssignmentPattern) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$] = '{1, 2};\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p1::q.size() * 10 + p1::q[1];\n"
                      "endmodule\n",
                      "y"),
            22u);
}

TEST(PackageImportSim, PackageAssociativeArrayInitializedWithADefault) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int m[string] = '{default: 7};\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p1::m[\"x\"];\n"
                      "endmodule\n",
                      "y"),
            7u);
}

TEST(PackageImportSim, PackageQueueOfAClassTypeHoldsHandles) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C q[$];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c1 = new;\n"
                      "    static C c2 = new;\n"
                      "    c1.v = 3;\n"
                      "    p1::q.push_back(c1);\n"
                      "    c2.v = 4;\n"
                      "    p1::q.push_back(c2);\n"
                      "    y = p1::q[1].v * 10 + p1::q[0].v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            43u);
}

TEST(PackageImportSim, PackageFixedSizeArrayInitializerReadingReExportedNames) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {VAL[3]} t;\n"
                      "  int x = 7;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int seen = VAL2 + x;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::*;\n"
                      "  int a[2] = '{VAL2, x};\n"
                      "  function int sum();\n"
                      "    return a[0] * 10 + a[1];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p3::sum();\n"
                      "endmodule\n",
                      "y"),
            27u);
}

TEST(PackageImportSim, PackageEventAwaitedThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  event e;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y = 0;\n"
                      "  initial #3 -> e;\n"
                      "  initial begin\n"
                      "    @(p1::e);\n"
                      "    y = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            3u);
}

TEST(PackageImportSim, PackageEventTriggeredStateWaitedOnThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  event e;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int z = 0;\n"
                      "  initial #3 -> e;\n"
                      "  initial begin\n"
                      "    wait (p1::e.triggered);\n"
                      "    z = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "z"),
            3u);
}

TEST(PackageImportSim, PackageEventTriggeredStateReadThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  event e;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    -> e;\n"
                      "    y = p1::e.triggered * 10 + p1::e.triggered();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11u);
}

TEST(PackageImportSim, PackageClassHandleCarrierIsSixtyFourBitsWide) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  class C;\n"
      "    int v;\n"
      "  endclass\n"
      "  C h;\n"
      "endpackage\n"
      "module top;\n"
      "  import p1::*;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* h = f.ctx.FindVariable("p1.h");
  ASSERT_NE(h, nullptr);
  EXPECT_EQ(h->value.width, 64u);
}

TEST(PackageImportSim, PackageClassHandleConstructedThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = (p1::h != null);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1u);
}

TEST(PackageScopeReferenceSim,
     PackageFunctionWithFormalsUnderOneTypeCalledQualified) {
  EXPECT_EQ(RunAndGet("package mypkg;\n"
                      "  function int add(int a, b);\n"
                      "    return a + b;\n"
                      "  endfunction\n"
                      "endpackage : mypkg\n"
                      "module top();\n"
                      "  int y;\n"
                      "  initial y = mypkg::add(1, 3);\n"
                      "endmodule\n",
                      "y"),
            4u);
}

}  // namespace
