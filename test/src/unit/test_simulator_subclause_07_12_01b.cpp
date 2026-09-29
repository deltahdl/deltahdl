#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

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

}  // namespace
