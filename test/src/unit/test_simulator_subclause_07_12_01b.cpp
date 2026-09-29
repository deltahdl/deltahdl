#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §7.12.1 with §7.4.4: over a two-dimensional array each element a locator
// visits is a row, which the with clause reduces (the row sums are 3 and 12),
// selects from (m[1][2] is 5) and reduces through a nested with clause, and
// each index locator reports the row's index. Read as 0, the iterator would
// match neither row of the first three queries and both rows of the last.
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

// §7.12.1: unique_index over the rows of a two-dimensional array keeps one
// index for each distinct value of the with clause, here the row sums 3, 3
// and 10, so two indices remain, the last of them row 2's.
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

// §7.12.1 with §7.4.4: over a three-dimensional array each element a locator
// visits is a two-dimensional subarray, from which the with clause selects:
// k[1][1][1] is the only leaf equal to 7.
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

// §7.12.1 with §7.4.2: the first element is the one closest to the leftmost
// index and the last the one closest to the rightmost, so on a[3:1] the first
// element above 5 is a[3] (30) and the last is a[1] (10), and over the rows of
// m[1:0][2] the first row whose sum is above 0 is row 1. Counted from the low
// index, each answer would come from the other end.
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

// §7.12.1 with §7.4.4: the locators that return elements return rows of a
// two-dimensional array, each a copy of the row's elements in the queue of
// rows they are assigned to: find keeps row 1, {3, 4, 5}, the one row whose
// sum passes 5; find_last and max pick row 1 and find_first and min row 0;
// and unique keeps one row for each of the sums 3 and 10, the last of them
// {5, 5}.
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

// §7.12.1: find requires a with clause over a two-dimensional array as over
// any other, and the call without one is reported once, on its line, when its
// result is assigned to a queue of rows.
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

}  // namespace
