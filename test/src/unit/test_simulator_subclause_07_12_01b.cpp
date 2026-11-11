#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayLocatorRows, IndexLocatorsSeeEachRowOfA2DArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int m[2][3];\n"
      "  int a[$], b[$], c[$], d[$];\n"
      "  initial begin\n"
      "    foreach (m[i, j]) m[i][j] = i * 3 + j;\n"
      "    a = m.find_index with (item.sum() > 5);\n"
      "    b = m.find_index with (item[2] == 5);\n"
      "    c = m.find_first_index with (item.sum with (item) > 5);\n"
      "    d = m.find_last_index(r) with (r[0] == 0);\n"
      "    $display(\"%p %p %p %p\", a, b, c, d);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{1} '{1} '{1} '{0}\n");
}

TEST(ArrayLocatorRows, UniqueIndexSeesEachRowOfA2DArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int u[3][2] = '{'{1, 2}, '{3, 0}, '{5, 5}};\n"
      "  int e[$];\n"
      "  initial begin\n"
      "    e = u.unique_index with (item.sum());\n"
      "    e.sort();\n"
      "    $display(\"%0d %0d\", e.size(), e[e.size() - 1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2\n");
}

TEST(ArrayLocatorRows, IndexLocatorsSeeEachSubarrayOfA3DArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int k[2][2][2];\n"
      "  int a[$];\n"
      "  initial begin\n"
      "    foreach (k[i, j, l]) k[i][j][l] = i * 4 + j * 2 + l;\n"
      "    a = k.find_index with (item[1][1] == 7);\n"
      "    $display(\"%p\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{1}\n");
}

TEST(ArrayLocatorRows, FirstAndLastFollowADescendingRange) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int a[3:1] = '{30, 20, 10};\n"
      "  int m[1:0][2] = '{'{1, 2}, '{3, 4}};\n"
      "  int f[$], fi[$], l[$], li[$], mi[$];\n"
      "  initial begin\n"
      "    f = a.find_first with (item > 5);\n"
      "    fi = a.find_first_index with (item > 5);\n"
      "    l = a.find_last with (item > 5);\n"
      "    li = a.find_last_index with (item > 5);\n"
      "    mi = m.find_first_index with (item.sum() > 0);\n"
      "    $display(\"%0d %0d %0d %0d %0d\", f[0], fi[0], l[0], li[0], "
      "mi[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "30 3 10 1 1\n");
}

TEST(ArrayLocatorRows, ElementLocatorsReturnTheRowsOfA2DArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int m[2][3];\n"
      "  int u[3][2] = '{'{1, 2}, '{3, 0}, '{5, 5}};\n"
      "  int r[$][3], s[$][3], l[$][3], w[$][3], x[$][3], y[$][2];\n"
      "  initial begin\n"
      "    foreach (m[i, j]) m[i][j] = i * 3 + j;\n"
      "    r = m.find with (item.sum() > 5);\n"
      "    s = m.find_first with (item[0] >= 0);\n"
      "    l = m.find_last with (item[0] >= 0);\n"
      "    w = m.max with (item.sum());\n"
      "    x = m.min with (item.sum());\n"
      "    y = u.unique with (item.sum());\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d %0d\", r.size(),\n"
      "             r[0][0], r[0][1], r[0][2], s[0][2], l[0][2], w[0][2],\n"
      "             x[0][2], y.size(), y[y.size() - 1][0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 3 4 5 2 5 5 2 2 5\n");
}

TEST(ArrayLocatorRows, FindWithoutAWithClauseIsReportedOnceIntoAQueueOfRows) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  int m[2][3];\n"
      "  int r[$][3];\n"
      "  initial begin\n"
      "    r = m.find;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array locator method 'find' requires a 'with' clause", 5, "7.12.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ArrayLocatorRows, LocatorsSeeEachElementOfAQueueOfArrays) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int s[$][3], w[$][3], x[$][3];\n"
      "  int qi[$];\n"
      "  initial begin\n"
      "    s.push_back('{4, 5, 6});\n"
      "    s.push_back('{1, 1, 1});\n"
      "    s.push_back('{0, 9, 0});\n"
      "    qi = s.find_index with (item.sum() > 5);\n"
      "    w = s.find with (item[1] == 9);\n"
      "    x = s.max with (item.sum());\n"
      "    $display(\"%p %0d %0d %0d %0d\", qi, w.size(), w[0][1], x.size(),\n"
      "             x[0][2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{0, 2} 1 9 1 6\n");
}

TEST(ArrayLocatorRows, ElementLocatorsReturnTheSubarraysOfA3DArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int k[2][2][2];\n"
      "  int r[$][2][2], s[$][2][2];\n"
      "  initial begin\n"
      "    foreach (k[i, j, l]) k[i][j][l] = i * 4 + j * 2 + l;\n"
      "    r = k.find with (item[1][1] == 7);\n"
      "    s = k.min with (item[0][0]);\n"
      "    $display(\"%0d %0d %0d %0d %0d\", r.size(), r[0][0][0], "
      "r[0][1][1],\n"
      "             s.size(), s[0][1][0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 4 7 1 2\n");
}

TEST(ArrayLocatorSubarray, LocatorsSearchTheElementsOfASubarraySelect) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int mg[2][4] = '{'{1, 2, 3, 4}, '{6, 4, 9, 4}};\n"
      "  int a[$], b[$], c[$], d[$], e[$], g[$], u[$], ui[$];\n"
      "  initial begin\n"
      "    a = mg[1].min();\n"
      "    b = mg[1].max();\n"
      "    c = mg[1].find(x) with (x > 5);\n"
      "    d = mg[1].find_index(x) with (x == 4);\n"
      "    e = mg[1].find_first_index with (item > 5);\n"
      "    g = mg[1].find_last with (item < 9);\n"
      "    u = mg[1].unique();\n"
      "    ui = mg[1].unique_index();\n"
      "    $display(\"%p %p %p %p %p %p %0d %0d\", a, b, c, d, e, g, u.size(), "
      "ui.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{4} '{9} '{6, 9} '{1, 3} '{0} '{4} 3 3\n");
}

TEST(ArrayLocatorSubarray, LocatorsSearchTheElementsOfAClassPropertysSubarray) {
  SimFixture f;
  auto out = RunCapture(
      "class H;\n"
      "  int g[2][4];\n"
      "  function int top(); int m[$]; m = g[1].max(); return m[0]; "
      "endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a[$], c[$], d[$], u[$];\n"
      "  initial begin\n"
      "    automatic H h = new;\n"
      "    h.g[1][0] = 6; h.g[1][1] = 4; h.g[1][2] = 9; h.g[1][3] = 4;\n"
      "    a = h.g[1].min();\n"
      "    c = h.g[1].find(x) with (x > 5);\n"
      "    d = h.g[1].find_index(x) with (x == 4);\n"
      "    u = h.g[1].unique();\n"
      "    $display(\"%p %p %p %0d %0d\", a, c, d, u.size(), h.top());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{4} '{6, 9} '{1, 3} 3 9\n");
}

TEST(ArrayLocatorResults,
     AssociativeLocatorsFollowTheKeyOrderAndIndexLocatorsReturnKeys) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  int aa[int];\n"
      "  byte unsigned ba[byte unsigned];\n"
      "  int q[$];\n"
      "  byte unsigned bq[$];\n"
      "  initial begin\n"
      "    aa[30] = 5; aa[-2] = 7; aa[10] = 5; aa[4] = 1;\n"
      "    ba[200] = 1; ba[7] = 2;\n"
      "    q = aa.unique_index; q.sort; $display(\"%p\", q);\n"
      "    q = aa.min; $display(\"%p\", q);\n"
      "    q = aa.max; $display(\"%p\", q);\n"
      "    q = aa.unique; q.sort; $display(\"%p\", q);\n"
      "    q = aa.find_first_index with (item == 5); $display(\"%p\", q);\n"
      "    q = aa.find_last_index with (item == 5); $display(\"%p\", q);\n"
      "    q = aa.find_first with (item > 3); $display(\"%p\", q);\n"
      "    q = aa.find_last with (item > 3); $display(\"%p\", q);\n"
      "    q = aa.find with (item); $display(\"%p\", q);\n"
      "    q = aa.find_index with (2.5 * item > 12.0); $display(\"%p\", q);\n"
      "    bq = ba.find_index with (item > 0);\n"
      "    $display(\"%0d %0d %0d\", bq.size(), bq[0], bq[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "'{-2, 4, 10}\n'{1}\n'{7}\n'{1, 5, 7}\n'{10}\n'{30}\n'{7}\n'{5}\n"
            "'{7, 1, 5, 5}\n'{-2, 10, 30}\n2 7 200\n");
}

TEST(ArrayLocatorResults,
     LocatorsOverAnEmptyArrayAndInsideAClassMethodReturnQueues) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  class C;\n"
      "    int v[4] = '{4, 9, 4, 1};\n"
      "    function int count();\n"
      "      int r[$];\n"
      "      r = v.unique_index;\n"
      "      return r.size();\n"
      "    endfunction\n"
      "    function int last();\n"
      "      int r[$];\n"
      "      r = v.find_last_index with (item == 4);\n"
      "      return r[0];\n"
      "    endfunction\n"
      "  endclass\n"
      "  int e[], q[$];\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    q = e.min; $write(\"%0d \", q.size());\n"
      "    q = e.max; $write(\"%0d \", q.size());\n"
      "    q = e.unique_index; $write(\"%0d \", q.size());\n"
      "    q = e.find_index with (item > 0); $write(\"%0d \", q.size());\n"
      "    q = e.find_last with (1); $write(\"%0d \", q.size());\n"
      "    $display(\"%0d %0d\", c.count(), c.last());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 0 0 0 0 3 2\n");
}

}  // namespace
