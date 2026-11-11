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

TEST(ArrayIteratorIndex,
     DISABLED_IndexMethodCalledWithParenthesesOrADimension) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int arr[] = '{0, 5, 2, 7};\n"
      "  int aa[int];\n"
      "  int m[2][3];\n"
      "  int q[$], r[$], s[$], u[$], w[$], z[$];\n"
      "  int d = 1;\n"
      "  initial begin\n"
      "    aa[3] = 3;\n"
      "    aa[4] = 9;\n"
      "    q = arr.find with (item == item.index());\n"
      "    r = arr.find with (item == item.index(1));\n"
      "    s = arr.find(x) with (x == x.index(d));\n"
      "    u = arr.find_index(x, i) with (x == x.i());\n"
      "    w = aa.find with (item == item.index());\n"
      "    z = arr.map with (item.index(1) * 2);\n"
      "    $display(\"%p %p %p %p %p %p\", q, r, s, u, w, z);\n"
      "    $display(\"%0d %0d\", arr.sum with (item.index()),\n"
      "             m.sum with (item.sum(y) with (y.index(1))));\n"
      "    arr.rsort with (item.index());\n"
      "    $display(\"%p\", arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "'{0, 2} '{0, 2} '{0, 2} '{0, 2} '{3} '{0, 2, 4, 6}\n"
            "6 6\n'{7, 2, 5, 0}\n");
}

TEST(ArrayIteratorIndex, DISABLED_IndexIsASignedIntAndAKeyKeepsItsSignedness) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int arr[] = '{3, 1, 2};\n"
      "  int fx[1:3] = '{1, 2, 3};\n"
      "  int ba[byte];\n"
      "  int sh[shortint];\n"
      "  int q[$], r[$];\n"
      "  initial begin\n"
      "    ba[-2] = 7;\n"
      "    ba[4] = 8;\n"
      "    sh[-300] = 5;\n"
      "    sh[6] = 6;\n"
      "    q = arr.find with (item.index - 1 < 0);\n"
      "    r = ba.find with (item.index < 0);\n"
      "    $display(\"%p %p %0d %0d\", q, r,\n"
      "             sh.sum with (int'(item.index < 0)),\n"
      "             fx.sum with (int'(item.index - 2 < 0)));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{3} '{7} 1 1\n");
}

TEST(ArrayIteratorIndex, IndexHasTheWidthOfTheKeyType) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int fx[1:3] = '{1, 2, 3};\n"
      "  int la[longint];\n"
      "  int ba[byte];\n"
      "  int na[bit [3:0]];\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    la[64'd1 << 40] = 5;\n"
      "    la[3] = 6;\n"
      "    ba[-2] = 7;\n"
      "    ba[4] = 8;\n"
      "    na[4'd15] = 9;\n"
      "    q = la.find with (item.index > 64'd1 << 39);\n"
      "    $display(\"%0d %p %0d %0d %0d\", $bits(fx.sum with (item.index)), "
      "q,\n"
      "             na.sum with (item.index + 1'b1),\n"
      "             ba.sum with ($bits(item.index)),\n"
      "             la.sum with ($bits(item.index)));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "32 '{5} 0 16 128\n");
}

TEST(ArrayIteratorIndex, RenamedIndexBesideAMemberOrPropertyNamedIndex) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct {int index; int v;} idx_type;\n"
      "  class C;\n"
      "    int index;\n"
      "  endclass\n"
      "  idx_type q[$];\n"
      "  idx_type r[$];\n"
      "  idx_type fa[4];\n"
      "  idx_type sa[int];\n"
      "  C cq[$];\n"
      "  int ix[$];\n"
      "  initial begin\n"
      "    q.push_back('{0, 10});\n"
      "    q.push_back('{5, 11});\n"
      "    q.push_back('{2, 12});\n"
      "    q.push_back('{9, 13});\n"
      "    r = q.find(item, iter_index) with (item.index != item.iter_index);\n"
      "    $display(\"%0d %0d %0d\", r.size(), r[0].v, r[1].v);\n"
      "    ix = q.find_index(item, p) with (item.index != item.p);\n"
      "    r = q.find_first(item, p) with (item.index != item.p);\n"
      "    $display(\"%p %0d %0d\", ix, r[0].v,\n"
      "             q.sum(item, p) with (item.index * item.p));\n"
      "    r = q.max(item, p) with (item.index - item.p);\n"
      "    $display(\"%0d\", r[0].v);\n"
      "    sa[7] = '{7, 1};\n"
      "    sa[8] = '{3, 2};\n"
      "    r = sa.find(item, k) with (item.index == item.k);\n"
      "    $display(\"%0d %0d\", r.size(), r[0].v);\n"
      "    fa = '{'{9, 10}, '{5, 11}, '{2, 12}, '{7, 13}};\n"
      "    fa.sort(item, p) with (item.index);\n"
      "    foreach (fa[i]) $write(\"%0d \", fa[i].v);\n"
      "    fa.rsort(item, p) with (item.p);\n"
      "    foreach (fa[i]) $write(\"%0d \", fa[i].v);\n"
      "    begin\n"
      "      C c;\n"
      "      c = new;\n"
      "      c.index = 0;\n"
      "      cq.push_back(c);\n"
      "      c = new;\n"
      "      c.index = 4;\n"
      "      cq.push_back(c);\n"
      "      c = new;\n"
      "      c.index = 2;\n"
      "      cq.push_back(c);\n"
      "    end\n"
      "    ix = cq.find_index(item, p) with (item.index != item.p);\n"
      "    $display(\"%p\", ix);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "2 11 13\n'{1, 3} 11 36\n13\n1 1\n12 11 13 10 10 13 11 12 "
            "'{1}\n");
}

TEST(ArrayIteratorIndex, DISABLED_RenamedIndexBesideAMethodNamedIndex) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class K;\n"
      "    int v;\n"
      "    function int index();\n"
      "      return v;\n"
      "    endfunction\n"
      "  endclass\n"
      "  K kq[$];\n"
      "  int ix[$];\n"
      "  initial begin\n"
      "    begin\n"
      "      K k;\n"
      "      k = new;\n"
      "      k.v = 0;\n"
      "      kq.push_back(k);\n"
      "      k = new;\n"
      "      k.v = 4;\n"
      "      kq.push_back(k);\n"
      "      k = new;\n"
      "      k.v = 2;\n"
      "      kq.push_back(k);\n"
      "    end\n"
      "    ix = kq.find_index(item, p) with (item.index() != item.p);\n"
      "    $display(\"%p %0d\", ix, kq.sum(item, p) with (item.index() * "
      "10));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{1} 60\n");
}

}  // namespace
