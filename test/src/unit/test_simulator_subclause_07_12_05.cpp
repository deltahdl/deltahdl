#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

bool RunProducesError(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  if (!design) return true;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  return f.diag.HasErrors();
}

uint32_t RunQueueElemWidth(const std::string& src, const char* qname,
                           size_t idx) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  auto* q = f.ctx.FindQueue(qname);
  EXPECT_NE(q, nullptr);
  if (!q || idx >= q->elements.size()) return 0;
  return q->elements[idx].width;
}

TEST(ArrayMap, ReplacesEachDynamicArrayElement) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int A[] = {1, 2, 3};\n"
      "  int v;\n"
      "  initial begin\n"
      "    A = A.map() with (item + 1'b1);\n"
      "    v = A[2];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 4u);
}

TEST(ArrayMap, PreservesElementCount) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int A[] = {10, 20, 30};\n"
      "  int R[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    R = A.map() with (item * 2);\n"
      "    sz = R.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 3u);
}

TEST(ArrayMap, ResultAssignedToQueueUsingIndex) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int A[] = {2, 3, 4};\n"
      "  int B[] = {2, 3, 5};\n"
      "  int C[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    C = A.map(a) with (a + B[a.index]);\n"
      "    v = C[2];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 9u);
}

TEST(ArrayMap, OverFixedSizeArray) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int fa[3] = '{3, 6, 9};\n"
      "  int R[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    R = fa.map() with (item * 2);\n"
      "    v = R[1];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 12u);
}

TEST(ArrayMap, OverQueueSource) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int q[$] = {5, 15, 25};\n"
      "  int R[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    R = q.map() with (item + 1);\n"
      "    v = R[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 6u);
}

TEST(ArrayMap, ElementTakesWithExpressionSelfDeterminedType) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  byte b[] = {8'h7F};\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    q = b.map() with (item << 4);\n"
      "    v = q[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 0xFFFFFFF0u);
}

TEST(ArrayMap, ElementTypeWiderThanSourceElement) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  byte b[] = {8'hFF};\n"
      "  int q[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    q = b.map() with (item * 256);\n"
      "    v = q[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 0xFFFFFF00u);
}

TEST(ArrayMap, ElementWidthIsWithExpressionWidth) {
  uint32_t w = RunQueueElemWidth(
      "module m;\n"
      "  int A[] = {1, 2, 3};\n"
      "  bit C[$];\n"
      "  initial C = A.map() with (item > 1);\n"
      "endmodule\n",
      "C", 0);
  EXPECT_EQ(w, 1u);
}

TEST(ArrayMap, BooleanComparisonElements) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int A[] = {2, 3, 9};\n"
      "  int B[] = {2, 3, 5};\n"
      "  bit C[];\n"
      "  int v;\n"
      "  initial begin\n"
      "    C = A.map(a) with (a == B[a.index]);\n"
      "    v = C[0] * 4 + C[1] * 2 + C[2];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 6u);
}

TEST(ArrayMap, EmptyDynamicSourceYieldsEmptyResult) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int A[];\n"
      "  int R[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    R = A.map() with (item + 1);\n"
      "    sz = R.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 0u);
}

TEST(ArrayMap, AssociativeSourcePreservesKeysReplacesValues) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[int];\n"
      "  int bb[int];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[10] = 5;\n"
      "    aa[20] = 15;\n"
      "    aa[30] = 25;\n"
      "    bb = aa.map(x) with (x + 1);\n"
      "    v = bb[20];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 16u);
}

TEST(ArrayMap, AssociativeSourcePreservesNonIntIndexType) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[shortint];\n"
      "  int bb[shortint];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[100] = 7;\n"
      "    aa[200] = 8;\n"
      "    bb = aa.map(x) with (x * 10);\n"
      "    v = bb[200];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 80u);
}

TEST(ArrayMap, AssociativeElementTakesWithExpressionSelfDeterminedType) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  byte aa[int];\n"
      "  int bb[int];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[7] = 8'h7F;\n"
      "    bb = aa.map(x) with (x << 4);\n"
      "    v = bb[7];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 0xFFFFFFF0u);
}

TEST(ArrayMap, StringKeyedAssociativeSourcePreservesKeys) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[string];\n"
      "  int bb[string];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[\"lo\"] = 5;\n"
      "    aa[\"hi\"] = 9;\n"
      "    bb = aa.map(x) with (x + 1);\n"
      "    v = bb[\"hi\"] + bb.size();\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 12u);
}

TEST(ArrayMap, EmptyAssociativeSourceYieldsEmptyResult) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int aa[int];\n"
      "  int bb[int];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    bb = aa.map(x) with (x + 1);\n"
      "    sz = bb.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 0u);
}

TEST(ArrayMap, IndexedSourceRequiresWithClause) {
  EXPECT_TRUE(
      RunProducesError("module m;\n"
                       "  int A[] = {1, 2, 3};\n"
                       "  int R[$];\n"
                       "  initial R = A.map();\n"
                       "endmodule\n"));
}

TEST(ArrayMap, AssociativeSourceRequiresWithClause) {
  EXPECT_TRUE(
      RunProducesError("module m;\n"
                       "  int aa[int];\n"
                       "  int bb[int];\n"
                       "  initial begin\n"
                       "    aa[1] = 5;\n"
                       "    bb = aa.map();\n"
                       "  end\n"
                       "endmodule\n"));
}

void RunForDiags(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
}

TEST(ArrayMap, IndexedSourceMissingWithNames7_12_5) {
  SimFixture f;
  RunForDiags(
      "module m;\n"
      "  int A[] = {4, 5};\n"
      "  int R[$];\n"
      "  initial R = A.map();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array method 'map' requires a 'with'", 4,
                            "7.12.5"));
}

TEST(ArrayMap, AssociativeSourceMissingWithNames7_12_5) {
  SimFixture f;
  RunForDiags(
      "module m;\n"
      "  int aa[int];\n"
      "  int bb[int];\n"
      "  initial begin\n"
      "    aa[2] = 6;\n"
      "    bb = aa.map();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array method 'map' requires a 'with'", 6,
                            "7.12.5"));
}

TEST(ArrayMap, MapOverTheRowsOfA2DArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int m[2][3];\n"
      "  int s[$];\n"
      "  initial begin\n"
      "    foreach (m[i, j]) m[i][j] = i * 3 + j;\n"
      "    s = m.map with (item.sum() + item[0]);\n"
      "    $display(\"%p\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{3, 15}\n");
}

TEST(ArrayMap, MapCalledFromEveryKindOfScope) {
  SimFixture f;
  auto out = RunCapture(
      "package p;\n"
      "  function automatic void twice(ref int a[$]);\n"
      "    a = a.map with (item * 2);\n"
      "  endfunction\n"
      "endpackage\n"
      "class C;\n"
      "  int v[] = '{4, 5};\n"
      "  int g[$];\n"
      "  function void step();\n"
      "    v = v.map with (item + item.index);\n"
      "    g = v.map(e) with (e * e.index);\n"
      "  endfunction\n"
      "endclass\n"
      "interface ifc;\n"
      "  int w[2] = '{7, 8};\n"
      "  int s[$];\n"
      "  initial begin\n"
      "    #1 s = w.map with (item - 1);\n"
      "    $display(\"%p\", s);\n"
      "  end\n"
      "endinterface\n"
      "program pr;\n"
      "  int u[$] = '{9};\n"
      "  initial begin\n"
      "    #4 u = u.map with (item + 100);\n"
      "    $display(\"%p\", u);\n"
      "  end\n"
      "endprogram\n"
      "module t;\n"
      "  import p::*;\n"
      "  ifc i();\n"
      "  pr pi();\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int fq[2] = '{20, 30};\n"
      "  int mq[$];\n"
      "  C c;\n"
      "  function automatic int total(int x[]);\n"
      "    int y[$];\n"
      "    y = x.map with (item * item);\n"
      "    return y.sum();\n"
      "  endfunction\n"
      "  for (genvar k = 1; k < 2; k++) begin : gb\n"
      "    initial begin\n"
      "      #3 mq = fq.map with (item + k);\n"
      "      $display(\"%p\", mq);\n"
      "    end\n"
      "  end\n"
      "  initial begin\n"
      "    twice(q);\n"
      "    c = new;\n"
      "    c.step();\n"
      "    $display(\"%p %p %p %0d\", q, c.v, c.g, total(d));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{2, 4, 6} '{4, 6} '{0, 6} 14\n'{6, 7}\n'{21, 31}\n'{109}\n");
}

TEST(ArrayMap, DISABLED_MapResultAssignedToAFixedSizeArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int fq[2] = '{20, 30};\n"
      "  int fz[2];\n"
      "  int fb[5:7] = '{1, 2, 3};\n"
      "  int fw[1:3];\n"
      "  int A[] = '{4, 5};\n"
      "  int fd[2];\n"
      "  initial begin\n"
      "    fz = fq.map with (item + 1);\n"
      "    fw = fb.map(e) with (e * 10 + e.index);\n"
      "    fd = A.map with (item - 1);\n"
      "    $display(\"%p %p %p\", fz, fw, fd);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{21, 31} '{15, 26, 37} '{3, 4}\n");
}

TEST(ArrayMap, DISABLED_MapOverADescendingRangeKeepsElementPositions) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int fa[3:1] = '{30, 60, 90};\n"
      "  int fb[5:7] = '{1, 2, 3};\n"
      "  int r[$], s[$], u[$];\n"
      "  initial begin\n"
      "    r = fa.map with (item);\n"
      "    s = fa.map with (item.index);\n"
      "    u = fb.map(e) with (e.index);\n"
      "    $display(\"%p %p %p\", r, s, u);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{30, 60, 90} '{3, 2, 1} '{5, 6, 7}\n");
}

TEST(ArrayMap, DISABLED_MapResultTakesTheSourceRange) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int fa[3:1] = '{30, 60, 90};\n"
      "  int fb[5:7] = '{1, 2, 3};\n"
      "  initial\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\",\n"
      "             $left(fa.map with (item)), $right(fa.map with (item)),\n"
      "             $size(fa.map with (item)), $left(fb.map with (item)),\n"
      "             $right(fb.map with (item)), $size(fb.map with (item)));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1 3 5 7 3\n");
}

TEST(ArrayMap, DISABLED_MapResultTakesTheSourceIndexType) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int aa[byte];\n"
      "  int yi[byte];\n"
      "  int sa[string];\n"
      "  int zi[string];\n"
      "  initial begin\n"
      "    aa[-1] = 1;\n"
      "    sa[\"k\"] = 5;\n"
      "    $display(\"%0d %0d\",\n"
      "             $typename(aa.map(v) with (v)) == $typename(yi),\n"
      "             $typename(sa.map(v) with (v)) == $typename(zi));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

TEST(ArrayMap, DISABLED_MapElementTypeIsTheSelfDeterminedTypeOfTheWith) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int fz[3] = '{1, 2, 3};\n"
      "  bit [3:0] w [3];\n"
      "  initial\n"
      "    $display(\"%0d %0d %0d\", $bits(fz.map with (item[3:0])),\n"
      "             $bits(fz.map with (item > 1)),\n"
      "             $typename(fz.map with (item[3:0])) == $typename(w));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "12 3 1\n");
}

TEST(ArrayMap, MapElementsAreSelfDeterminedNotWidenedByTheTarget) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  byte b[] = {8'h80, 8'h01};\n"
      "  int A[] = {-1, 3};\n"
      "  int q[$];\n"
      "  real rq[$];\n"
      "  string sq[$];\n"
      "  initial begin\n"
      "    q = b.map with (item + 8'd0);\n"
      "    $display(\"%p\", q);\n"
      "    q = b.map with (item + item);\n"
      "    $display(\"%p\", q);\n"
      "    q = A.map with (item[3:0]);\n"
      "    $display(\"%p\", q);\n"
      "    rq = A.map with (item * 0.5);\n"
      "    $display(\"%p\", rq);\n"
      "    sq = A.map with ($sformatf(\"<%0d>\", item));\n"
      "    $display(\"%p\", sq);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "'{128, 1}\n'{0, 2}\n'{15, 3}\n'{-0.5, 1.5}\n"
            "'{\"<-1>\", \"<3>\"}\n");
}

TEST(ArrayMap, DISABLED_MapAssignedBackToItsOwnPropertyThroughANamedIterator) {
  SimFixture f;
  auto out = RunCapture(
      "class C;\n"
      "  int v[] = '{4, 5};\n"
      "  int r[$] = '{4, 5};\n"
      "  function void step();\n"
      "    v = v.map(e) with (e * 10);\n"
      "    r = r.map(e) with (e + e.index);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    c.step();\n"
      "    $display(\"%p %p\", c.v, c.r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{40, 50} '{4, 6}\n");
}

TEST(ArrayMap, MapWithoutAWithClauseIsReportedForEveryIndexedKind) {
  SimFixture f;
  RunForDiags(
      "module m;\n"
      "  int A[] = {1, 2};\n"
      "  int fz[2] = '{1, 2};\n"
      "  int q[$] = {3};\n"
      "  int R[$];\n"
      "  initial begin\n"
      "    R = A.map;\n"
      "    R = fz.map();\n"
      "    R = q.map;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (int line : {7, 8, 9}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "array method 'map' requires a 'with'", line,
                              "7.12.5"));
  }
}

}  // namespace
