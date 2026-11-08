#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AssocArraySimulation, DynamicElementCreation) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArraySimulation, MultipleElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[2] = 20;\n"
      "    aa[3] = 30;\n"
      "    result = aa[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocArraySimulation, OverwriteElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[7] = 100;\n"
      "    aa[7] = 200;\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

TEST(AssocArraySimulation, NoStorageAllocatedUntilUsed) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial result = aa.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArraySimulation, RefArgAllocatesNonexistentEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  task automatic inc_ref(ref int x);\n"
      "    x = x + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    inc_ref(aa[5]);\n"
      "    result = aa.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArraySimulation, VectorElementStoredAndRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 8'hAB;\n"
      "    result = aa[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

TEST(AssocArraySimulation, WholeArrayCopyDuplicatesEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int bb[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 77;\n"
      "    bb = aa;\n"
      "    result = bb[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

TEST(AssocArraySimulation, AssocElementWriteWakesAnEventControlOnThatElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  int woke;\n"
      "  always @(aa[3]) woke = woke + 1;\n"
      "  initial begin\n"
      "    woke = 0;\n"
      "    #1 aa[3] = 8'hF0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "woke");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArraySimulation,
     AssocElementBitSelectWriteWakesAnEventControlOnThatElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  int woke;\n"
      "  always @(aa[3]) woke = woke + 1;\n"
      "  initial begin\n"
      "    woke = 0;\n"
      "    #1 aa[3] = 8'hF0;\n"
      "    #1 aa[3][3:0] = 4'hA;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "woke");
  EXPECT_EQ(v, 2u);
}

TEST(AssocArraySimulation, AssocElementWriteWakesAnAlwaysCombThatReadsIt) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  logic [7:0] b;\n"
      "  always_comb b = aa[3];\n"
      "  initial begin\n"
      "    #1 aa[3] = 8'hF0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(v, 0xF0u);
}

TEST(AssocArraySimulation, ADeclarationInsideAFunctionBuildsTheArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int keep();\n"
      "    int aa [int];\n"
      "    aa[7] = 42;\n"
      "    return aa[7];\n"
      "  endfunction\n"
      "  initial result = keep();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArraySimulation, ACopyBetweenTwoDeclaredInsideAFunction) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int copy();\n"
      "    int src [int];\n"
      "    int dst [int];\n"
      "    src[7] = 42;\n"
      "    dst = src;\n"
      "    return dst[7];\n"
      "  endfunction\n"
      "  initial result = copy();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArraySimulation, AStringKeyedArrayInsideAFunctionKeysByTheString) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  function int keyed();\n"
      "    int aa [string];\n"
      "    aa[\"seven\"] = 42;\n"
      "    return aa[\"seven\"];\n"
      "  endfunction\n"
      "  initial result = keyed();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArraySimulation, TheSameDeclarationAmongAModulesItemsStillBuildsOne) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa [int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[7] = 42;\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArraySimulation,
     AMemberSelectedOnAnElementOfADeclaredArrayOfHandlesReadsItsObject) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int x); v = x; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C m[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    m[\"a\"] = new(5);\n"
      "    m[\"b\"] = new(6);\n"
      "    result = m[\"a\"].v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

TEST(AssocArraySimulation,
     AMethodCalledOnAnElementOfADeclaredArrayOfHandlesRunsOnItsObject) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int x); v = x; endfunction\n"
      "  function int m(); return v + 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C m[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    m[\"a\"] = new(5);\n"
      "    m[\"b\"] = new(7);\n"
      "    result = m[\"a\"].m();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

TEST(AssocArraySimulation,
     AnIntKeyedArrayOfHandlesReachesTheObjectUnderEachKey) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int x); v = x; endfunction\n"
      "  function int m(); return v + 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C q[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q[3] = new(7);\n"
      "    q[4] = new(9);\n"
      "    result = q[3].v * 10 + q[4].m();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 80u);
}

TEST(AssocArraySimulation, ChildInstanceIntKeyedArrayHoldsItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  int aa[int];\n"
      "  int r;\n"
      "  initial begin\n"
      "    aa[5] = 42;\n"
      "    aa[9] = 17;\n"
      "    r = aa[9] * 100 + aa.num();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1702u);
}

TEST(AssocArraySimulation, ChildInstanceStringKeyedArrayHoldsItsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  int sa[string];\n"
      "  int r, s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    sa[\"k\"] = 3;\n"
      "    sa[\"j\"] = 4;\n"
      "    sa[\"l\"] = 5;\n"
      "    foreach (sa[key]) s = s + sa[key];\n"
      "    r = sa.size() * 100 + s;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 312u);
}

static std::string AssocPropertyDesign(std::string_view rest) {
  return "class C;\n"
         "  int v;\n"
         "  function new(int x); v = x; endfunction\n"
         "endclass\n"
         "class H;\n"
         "  C m[string];\n"
         "  function int go();\n"
         "    m[\"b\"] = new(5);\n"
         "    return m[\"b\"].v;\n"
         "  endfunction\n"
         "endclass\n" +
         std::string(rest);
}

TEST(AssocArraySimulation, AssocPropertyOfHandlesConstructedThroughAHandle) {
  EXPECT_EQ(RunAndGet(AssocPropertyDesign("module t;\n"
                                          "  H x = new;\n"
                                          "  int result;\n"
                                          "  initial begin\n"
                                          "    x.m[\"a\"] = new(5);\n"
                                          "    result = x.m[\"a\"].v;\n"
                                          "  end\n"
                                          "endmodule\n"),
                      "result"),
            5u);
}

TEST(AssocArraySimulation, AssocPropertyOfHandlesConstructedInAMethod) {
  EXPECT_EQ(RunAndGet(AssocPropertyDesign("module t;\n"
                                          "  H x = new;\n"
                                          "  int result;\n"
                                          "  initial result = x.go();\n"
                                          "endmodule\n"),
                      "result"),
            5u);
}

TEST(AssocArraySimulation, ModuleVariableThroughAnAssocTypedefIsAnAssocArray) {
  SimFixture f;
  auto out = RunCapture(
      "typedef bit ie_t[int];\n"
      "module t;\n"
      "  ie_t x;\n"
      "  initial begin\n"
      "    x[5] = 1;\n"
      "    x[9] = 1;\n"
      "    $display(\"num=%0d\", x.num());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "num=2\n");
}

TEST(AssocArraySimulation, ProceduralLocalThroughAnAssocTypedefIsAnAssocArray) {
  SimFixture f;
  auto out = RunCapture(
      "typedef bit ie_t[int];\n"
      "module t;\n"
      "  initial begin\n"
      "    ie_t y;\n"
      "    y[2] = 1;\n"
      "    y[7] = 1;\n"
      "    y[11] = 1;\n"
      "    $display(\"num=%0d\", y.num());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "num=3\n");
}

TEST(AssocArraySimulation, MethodLocalThroughAUnitAssocTypedefIsAnAssocArray) {
  SimFixture f;
  auto out = RunCapture(
      "typedef bit ue_t[int];\n"
      "class K;\n"
      "  function int f();\n"
      "    ue_t u;\n"
      "    u[3] = 1;\n"
      "    u[4] = 1;\n"
      "    return u.num();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin static K k = new; $display(\"num=%0d\", k.f()); end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "num=2\n");
}

TEST(AssocArraySimulation, AssocOfAssocKeepsAnInnerArrayPerKey) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int m[string][int];\n"
      "  initial begin\n"
      "    m[\"a\"][1] = 41; m[\"a\"][2] = 42; m[\"b\"][9] = 9;\n"
      "    $display(\"%0d %0d %0d %0d\", m.num(), m[\"a\"].num(), "
      "m[\"b\"].num(),\n"
      "             m[\"a\"][2]);\n"
      "    $display(\"%0d %0d %0d\", m[\"a\"].exists(2), m[\"b\"].exists(2),\n"
      "             m[\"b\"][9]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2 1 42\n1 0 9\n");
}

TEST(AssocArraySimulation, AnElementReadsWithTheElementTypesSignedness) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int aa[int];\n"
      "  int as[string];\n"
      "  bit [31:0] ua[int];\n"
      "  int mm[string][int];\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    int ba[int];\n"
      "    bit [31:0] bu[int];\n"
      "    u = 32'hFFFFFFFD;\n"
      "    aa[0] = u; as[\"k\"] = u; ua[0] = -3; mm[\"k\"][0] = u;\n"
      "    ba[0] = u; bu[0] = -3;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", aa[0] < 0, as[\"k\"] < 0,\n"
      "             ua[0] < 0, mm[\"k\"][0] < 0, ba[0] < 0, bu[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 0 1 1 0\n");
}

TEST(AssocArraySimulation, AStringOrRealElementReadsAsItsOwnType) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string sa[int];\n"
      "  real ra[string];\n"
      "  string s = \"hey\";\n"
      "  real r = -1.25;\n"
      "  initial begin\n"
      "    sa[1] = s; ra[\"k\"] = r;\n"
      "    $display(\"%s %0.2f %0d\", sa[1], ra[\"k\"], ra[\"k\"] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "hey -1.25 1\n");
}

TEST(AssocArraySimulation, AStringMethodReadsTheElementsText) {
  SimFixture f;
  auto out = RunCapture(
      "package p;\n"
      "  string ps[int];\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  string sa[int];\n"
      "  string sk[string];\n"
      "  initial begin\n"
      "    string sb[byte];\n"
      "    sa[1] = \"hi\"; sk[\"k\"] = \"wxyz\"; sb[2] = \"abc\";\n"
      "    ps[0] = \"pqrst\";\n"
      "    $display(\"%0d %0d %0d %0d\", sa[1].len(), sk[\"k\"].len(),\n"
      "             sb[2].len(), ps[0].len());\n"
      "    $display(\"%s %s %0d\", sa[1].toupper(), sk[\"k\"].substr(1, 2),\n"
      "             sb[2].getc(1));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 4 3 5\nHI xy 98\n");
}

TEST(AssocArraySimulation, AnElementOfAPackageAssociativeArrayReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "package p;\n"
      "  int aa[int];\n"
      "endpackage\n"
      "module t;\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hFFFFFFFD;\n"
      "    p::aa[0] = u;\n"
      "    $display(\"%0d\", p::aa[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(AssocArraySimulation, AnElementOfAnAssociativeArrayFormalReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int x[int];\n"
      "  bit [31:0] u;\n"
      "  function int negative(int a[int]);\n"
      "    return a[0] < 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = 32'hFFFFFFFD;\n"
      "    x[0] = u;\n"
      "    $display(\"%0d\", negative(x));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(AssocArraySimulation, AnElementOfAnAssociativeArrayPropertyReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C;\n"
      "    int m[int];\n"
      "  endclass\n"
      "  C c, d;\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hFFFFFFFD;\n"
      "    c = new;\n"
      "    c.m[0] = u;\n"
      "    d = new c;\n"
      "    $display(\"%0d %0d\", c.m[0] < 0, d.m[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

TEST(AssocArraySimulation, ElementsThatAreFixedSizeArraysKeepTheirValues) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int af[int][2];\n"
      "  logic [3:0] lf[string][1:0];\n"
      "  int am[int][2][3];\n"
      "  int row[2];\n"
      "  initial begin\n"
      "    af[1][0] = 5; af[1][1] = 6; af[4] = '{7, 8};\n"
      "    lf[\"a\"][1] = 4'h3;\n"
      "    am[0][1][2] = 9;\n"
      "    row = af[4];\n"
      "    $display(\"%0d %0d %0d %0d %0d\", af.num(), af[1][0], af[1][1],\n"
      "             af[4][0], row[1]);\n"
      "    $display(\"%p %p %p\", af, lf, am);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "2 5 6 7 8\n"
            "'{1:'{5, 6}, 4:'{7, 8}} '{\"a\":'{3, x}} "
            "'{0:'{'{0, 0, 0}, '{0, 0, 9}}}\n");
}

}  // namespace
