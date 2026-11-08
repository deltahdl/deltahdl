#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PackageImportSim, ImportedPackageFixedSizeArrayElementWrittenAndRead) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "  function int get(int i);\n"
                      "    return a[i];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    a[1] = 7;\n"
                      "    y = a[1] * 10 + get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            77u);
}

TEST(PackageImportSim, ImportedPackageFixedSizeArrayCountedByForeach) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int n = 0;\n"
                      "  initial foreach (a[i]) n++;\n"
                      "endmodule\n",
                      "n"),
            2u);
}

TEST(PackageImportSim, ImportedPackageFixedSizeArraySizeQueried) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial y = $size(a);\n"
                      "endmodule\n",
                      "y"),
            2u);
}

TEST(PackageImportSim, ImportedPackageDynamicArraySizedByPackageFunction) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int d[];\n"
                      "  function void make();\n"
                      "    p1::d = new[3];\n"
                      "    p1::d[2] = 4;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    make();\n"
                      "    y = d.size() * 10 + d[2];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(PackageImportSim, ExportedPackageFixedSizeArrayReadThroughTheExporter) {
  EXPECT_EQ(
      RunAndGet("package p1;\n"
                "  int a[2];\n"
                "  function void set(int i, int v);\n"
                "    a[i] = v;\n"
                "  endfunction\n"
                "endpackage\n"
                "package p2;\n"
                "  import p1::*;\n"
                "  export p1::*;\n"
                "  function automatic int seen(); return a[0]; endfunction\n"
                "endpackage\n"
                "module top;\n"
                "  import p2::*;\n"
                "  int n = 0;\n"
                "  int y;\n"
                "  initial begin\n"
                "    p1::set(1, 5);\n"
                "    foreach (p2::a[i]) n++;\n"
                "    y = a[1] * 10 + n;\n"
                "  end\n"
                "endmodule\n",
                "y"),
      52u);
}

TEST(PackageImportSim,
     GenerateBlockImportedArrayElementAndQueueReadByThePackage) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int a[2];\n"
                      "  int q[$];\n"
                      "  function int get(int i);\n"
                      "    return a[i];\n"
                      "  endfunction\n"
                      "  function int qs();\n"
                      "    return q.size();\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  if (1) begin : blk\n"
                      "    import p1::*;\n"
                      "    initial begin\n"
                      "      a[1] = 7;\n"
                      "      q.push_back(2);\n"
                      "      q.push_back(3);\n"
                      "    end\n"
                      "  end\n"
                      "  initial #1 y = p1::get(1) * 10 + p1::qs();\n"
                      "endmodule\n",
                      "y"),
            72u);
}

TEST(PackageImportSim, GenerateBlockImportedArrayCountedByForeach) {
  EXPECT_EQ(RunAndGet("package p2;\n"
                      "  int a[3];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int n = 0;\n"
                      "  if (1) begin : g\n"
                      "    import p2::*;\n"
                      "    initial foreach (a[i]) n++;\n"
                      "  end\n"
                      "endmodule\n",
                      "n"),
            3u);
}

TEST(PackageImportSim, GenerateBlockImportedArraySizeQueried) {
  EXPECT_EQ(RunAndGet("package p3;\n"
                      "  int a[2];\n"
                      "  int b[4];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  if (1) begin : blk\n"
                      "    import p3::*;\n"
                      "    initial y = $size(a) * 10 + $size(b);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            24u);
}

TEST(PackageImportSim, GenerateBlockImportedArrayElementReadInTheBlock) {
  EXPECT_EQ(RunAndGet("package p4;\n"
                      "  int a[2];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y2;\n"
                      "  if (1) begin : blk\n"
                      "    import p4::*;\n"
                      "    initial begin\n"
                      "      a[1] = 7;\n"
                      "      a[0] = 3;\n"
                      "      y2 = a[1] * 10 + a[0];\n"
                      "    end\n"
                      "  end\n"
                      "endmodule\n",
                      "y2"),
            73u);
}

static uint64_t PackageStructRead(const std::string& top_items) {
  return RunAndGet(
      "package p5;\n"
      "  typedef struct packed { logic [3:0] a; logic [11:0] b; } st2;\n"
      "  st2 u = '{b: 12'hBCD, a: 4'hA};\n"
      "endpackage\n"
      "module top;\n" +
          top_items + "endmodule\n",
      "y");
}

TEST(PackageImportSim, PackageStructVariableMemberReadThroughItsScopedName) {
  EXPECT_EQ(PackageStructRead("  int y;\n"
                              "  initial y = p5::u.b;\n"),
            0xBCDu);
}

TEST(PackageImportSim, ImportedPackageStructVariableMemberReadByItsBareName) {
  EXPECT_EQ(PackageStructRead("  import p5::*;\n"
                              "  int y;\n"
                              "  initial y = u.b;\n"),
            0xBCDu);
}

TEST(PackageImportSim,
     ImportedPackageTaggedUnionRetaggedByItsBareNameIsOneTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p6;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u = tagged Valid 9;\n"
      "endpackage\n"
      "module top;\n"
      "  import p6::*;\n"
      "  int y;\n"
      "  initial begin\n"
      "    u = tagged Other 3;\n"
      "    y = p6::u.Valid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  Variable* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "run-time error: accessing member 'Valid' of tagged union 'p6.u' "
      "which currently has tag 'Other'",
      10, "11.9"));
}

TEST(PackageImportSim, UninitializedPackageVariablesHoldTheirTypesDefaults) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package P;\n"
          "  logic pl; int pn; string ps; real pr;\n"
          "endpackage\n"
          "module t;\n"
          "  import P::*;\n"
          "  initial begin\n"
          "    $display(\"pl=%0h pn=%0d ps=[%s] pr=%f\", pl, pn, ps, pr);\n"
          "    $display(\"ql=%0h qn=%0d qs=[%s] qr=%f\", P::pl, P::pn,\n"
          "             P::ps, P::pr);\n"
          "  end\n"
          "endmodule\n",
          f),
      "pl=x pn=0 ps=[] pr=0.000000\nql=x qn=0 qs=[] qr=0.000000\n");
}

TEST(PackageImportSim, ImportedPackageVariableIsAnAssignmentTarget) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package P; int pn; endpackage\n"
                       "module t;\n"
                       "  import P::*;\n"
                       "  logic [3:0] lv = 4'bx1z1;\n"
                       "  initial begin\n"
                       "    P::pn = 17;\n"
                       "    $display(\"a=%0d b=%0d\", pn, P::pn);\n"
                       "    pn = 23;\n"
                       "    $display(\"c=%0d d=%0d\", pn, P::pn);\n"
                       "    pn = lv;\n"
                       "    $display(\"e=%0d\", P::pn);\n"
                       "    pn = 1.5;\n"
                       "    $display(\"f=%0d\", P::pn);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "a=17 b=17\nc=23 d=23\ne=5\nf=2\n");
}

TEST(PackageImportSim, BlockReferenceBeforeItsDeclarationReadsTheImport) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p; int q = 5; endpackage\n"
                 "module m;\n"
                 "  import p::*;\n"
                 "  if (1) begin : s1\n"
                 "    initial begin #1 $display(\"r=%0d\", q); q = 7; end\n"
                 "    int q = 9;\n"
                 "  end\n"
                 "  initial #2 $display(\"p=%0d b=%0d\", p::q, s1.q);\n"
                 "endmodule\n",
                 f),
      "r=5\np=7 b=9\n");
}

TEST(PackageImportSim, UnimportedPackageClassLeavesTheBuiltinName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  class semaphore;\n"
                       "    int keys;\n"
                       "  endclass\n"
                       "endpackage\n"
                       "module m;\n"
                       "  semaphore s[string];\n"
                       "  int a, b;\n"
                       "  initial begin\n"
                       "    s[\"k\"] = new(1);\n"
                       "    a = s[\"k\"].try_get(1);\n"
                       "    b = s[\"k\"].try_get(1);\n"
                       "    $display(\"a=%0d b=%0d\", a, b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "a=1 b=0\n");
}

TEST(PackageImportSim, PackageClassMethodNamesItsClassBare) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  class Node;\n"
                       "    int v;\n"
                       "    Node next;\n"
                       "    function void grow(int x);\n"
                       "      Node n = new;\n"
                       "      n.v = x;\n"
                       "      next = n;\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "endpackage\n"
                       "module m;\n"
                       "  p::Node h = new;\n"
                       "  initial begin\n"
                       "    h.grow(4);\n"
                       "    $display(\"v=%0d\", h.next.v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "v=4\n");
}

TEST(PackageImportSim, ReadBeforeTheWildcardImportReachesTheUnitsData) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "package p; int c = 2; endpackage\n"
          "int c = 7;\n"
          "module m;\n"
          "  int y, z;\n"
          "  initial begin y = c; end\n"
          "  import p::*;\n"
          "  initial begin #1 z = c; $display(\"y=%0d z=%0d\", y, z); end\n"
          "endmodule\n",
          f),
      "y=7 z=2\n");
}

TEST(PackageImportSim, NetOfAnImportedNettypeResolvesThroughThePackagesFunc) {
  EXPECT_EQ(RunAndGet("package P;\n"
                      "  function automatic logic [3:0] pres(input logic [3:0] "
                      "d[]);\n"
                      "    pres = 4'hf;\n"
                      "    foreach (d[i]) pres = pres & d[i];\n"
                      "  endfunction\n"
                      "  nettype logic [3:0] nt with pres;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import P::*;\n"
                      "  nt n;\n"
                      "  logic [3:0] y;\n"
                      "  assign n = 4'h3;\n"
                      "  assign n = 4'h5;\n"
                      "  initial #1 y = n;\n"
                      "endmodule\n",
                      "y"),
            1u);
}

}  // namespace
