#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ArrayIteratorIndex, DefaultIndexSelectsByPositionInFind) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {100, 200, 300};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find with (item.index > 0);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 200u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFindIndex) {
  uint64_t p = RunAndGet(
      "module m;\n"
      "  int arr[] = {100, 200, 300};\n"
      "  int idx[$];\n"
      "  int p;\n"
      "  initial begin\n"
      "    idx = arr.find_index with (item.index > 0);\n"
      "    p = idx[1];\n"
      "  end\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(p, 2u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFindFirst) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 10, 15, 20};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find_first with (item.index >= 2);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 15u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFindLast) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 10, 15, 20};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find_last with (item.index < 2);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 10u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFindFirstIndex) {
  uint64_t p = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 10, 15, 20};\n"
      "  int idx[$];\n"
      "  int p;\n"
      "  initial begin\n"
      "    idx = arr.find_first_index with (item.index > 1);\n"
      "    p = idx[0];\n"
      "  end\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(p, 2u);
}

TEST(ArrayIteratorIndex, DefaultIndexInFindLastIndex) {
  uint64_t p = RunAndGet(
      "module m;\n"
      "  int arr[] = {5, 10, 15, 20};\n"
      "  int idx[$];\n"
      "  int p;\n"
      "  initial begin\n"
      "    idx = arr.find_last_index with (item.index < 3);\n"
      "    p = idx[0];\n"
      "  end\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(p, 2u);
}

TEST(ArrayIteratorIndex, IndexComparedToElementValue) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int arr[] = {2, 1, 2, 9};\n"
      "  int found[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    found = arr.find with (item == item.index);\n"
      "    sz = found.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 2u);
}

TEST(ArrayIteratorIndex, DefaultIndexOverFixedArray) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  logic [7:0] a [0:2] = '{8'd10, 8'd20, 8'd30};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = a.find with (item.index >= 1);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 20u);
}

TEST(ArrayIteratorIndex, IndexIsIntForNonAssociative) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {42, 99, 7};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find with (item.index * 1000 >= 2000);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 7u);
}

TEST(ArrayIteratorIndex, AssociativeIndexReturnsKey) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int aa[int];\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    aa[10] = 100;\n"
      "    aa[20] = 200;\n"
      "    aa[30] = 300;\n"
      "    found = aa.find with (item.index == 20);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 200u);
}

TEST(ArrayIteratorIndex, RenamedIndexArgumentInFind) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {10, 20, 30, 40};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find(elem, pos) with (elem.pos < 2);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 10u);
}

TEST(ArrayIteratorIndex, RenamedIndexArgumentInFindIndex) {
  uint64_t p = RunAndGet(
      "module m;\n"
      "  int arr[] = {100, 200, 300};\n"
      "  int idx[$];\n"
      "  int p;\n"
      "  initial begin\n"
      "    idx = arr.find_index(x, i) with (x.i > 0);\n"
      "    p = idx[1];\n"
      "  end\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(p, 2u);
}

TEST(ArrayIteratorIndex, EmptyArrayIndexKeepsNothing) {
  uint64_t sz = RunAndGet(
      "module m;\n"
      "  int arr[];\n"
      "  int found[$];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    found = arr.find with (item.index >= 0);\n"
      "    sz = found.size();\n"
      "  end\n"
      "endmodule\n",
      "sz");
  EXPECT_EQ(sz, 0u);
}

TEST(ArrayIteratorIndex, SingleElementIndexIsZero) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int arr[] = {77};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = arr.find with (item.index == 0);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 77u);
}

TEST(ArrayIteratorIndex, IndexOverQueue) {
  uint64_t v = RunAndGet(
      "module m;\n"
      "  int q [$] = {5, 15, 25, 35};\n"
      "  int found[$];\n"
      "  int v;\n"
      "  initial begin\n"
      "    found = q.find with (item.index >= 2);\n"
      "    v = found[0];\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(v, 25u);
}

TEST(ArrayIteratorIndex, IndexInReductionMethod) {
  uint64_t r = RunAndGet(
      "module m;\n"
      "  int arr[] = {50, 60, 70};\n"
      "  int r;\n"
      "  initial r = arr.sum() with (item.index);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 3u);
}

TEST(ArrayIteratorIndex, IndexOfAFixedArrayNotStartingAtZero) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int a[1:3] = '{10, 20, 30};\n"
      "  int m[1:2][3];\n"
      "  int b[$], c[$], d[$], e[$], g[$], h[$], k[$];\n"
      "  initial begin\n"
      "    foreach (m[i, j]) m[i][j] = (i - 1) * 3 + j;\n"
      "    b = a.find_index with (item == 20);\n"
      "    c = a.find_index with (item.index == 2);\n"
      "    d = a.find_last_index with (item > 15);\n"
      "    e = a.map with (item.index);\n"
      "    g = a.unique_index;\n"
      "    g.sort();\n"
      "    h = a.unique_index with (item > 15);\n"
      "    h.sort();\n"
      "    k = m.find_index with (item.sum() > 5);\n"
      "    $display(\"%p %p %p %p %p %0d %p %0d\", b, c, d, e, g, h[0], k,\n"
      "             a.sum with (item.index));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{2} '{2} '{3} '{1, 2, 3} '{1, 2, 3} 1 '{2} 6\n");
}

TEST(ArrayIteratorIndex, SortKeyReadsTheDeclaredIndex) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int s[1:3] = '{10, 20, 30};\n"
      "  initial begin\n"
      "    s.rsort with (int'(item.index == 1));\n"
      "    $display(\"%p\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{10, 20, 30}\n");
}

TEST(ArrayIteratorIndex, AssociativeReductionIndexIsTheKey) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int aa[int];\n"
      "  int sa[string];\n"
      "  initial begin\n"
      "    aa[5] = 1;\n"
      "    aa[9] = 2;\n"
      "    sa[\"b\"] = 1;\n"
      "    sa[\"a\"] = 2;\n"
      "    $display(\"%0d %0d\", aa.sum with (item.index),\n"
      "             sa.sum with (item.index == \"a\" ? 10 : 1));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "14 11\n");
}

}  // namespace
