#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §10.9.1 assigns an array assignment pattern to an unpacked array element by
// element, §7.5 gives a dynamic array assigned whole the size of what is
// assigned, and §8.5 lets a dynamic array be a class property. So a pattern
// assigned to one, through a handle or by its bare name in a method, stores
// each item, and a shorter pattern shortens it. The pattern wrote nothing:
// the elements stayed 0 and the size 3.
TEST(ArrayLiteralSim, APatternFillsADynamicArrayProperty) {
  const char* src =
      "module t;\n"
      "  class P;\n"
      "    byte d[];\n"
      "    function void f(); d = new[3]; d = '{4, 5, 6}; endfunction\n"
      "  endclass\n"
      "  P p;\n"
      "  int n, e0, e1, e2, m0, m2, shorter;\n"
      "  initial begin\n"
      "    p = new;\n"
      "    p.d = new[3];\n"
      "    p.d = '{1, 2, 3};\n"
      "    n = p.d.size(); e0 = p.d[0]; e1 = p.d[1]; e2 = p.d[2];\n"
      "    p.f();\n"
      "    m0 = p.d[0]; m2 = p.d[2];\n"
      "    p.d = '{1, 2};\n"
      "    shorter = p.d.size();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 3u);
  EXPECT_EQ(RunAndGet(src, "e0"), 1u);
  EXPECT_EQ(RunAndGet(src, "e1"), 2u);
  EXPECT_EQ(RunAndGet(src, "e2"), 3u);
  EXPECT_EQ(RunAndGet(src, "m0"), 4u);
  EXPECT_EQ(RunAndGet(src, "m2"), 6u);
  EXPECT_EQ(RunAndGet(src, "shorter"), 2u);
}

// §10.9.1's replication `'{3{7, 8}}` gives the items it repeats as many times
// as it says, so a dynamic array property it is assigned to holds six
// elements alternating 7 and 8, from an empty one.
TEST(ArrayLiteralSim, AReplicationSizesADynamicArrayProperty) {
  const char* src =
      "module t;\n"
      "  class P; int d[]; endclass\n"
      "  P p;\n"
      "  int n, e4, e5;\n"
      "  initial begin\n"
      "    p = new;\n"
      "    p.d = '{3{7, 8}};\n"
      "    n = p.d.size(); e4 = p.d[4]; e5 = p.d[5];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 6u);
  EXPECT_EQ(RunAndGet(src, "e4"), 7u);
  EXPECT_EQ(RunAndGet(src, "e5"), 8u);
}

// §10.9.1 with §7.5 and §8.7: a dynamic array property declared with an
// assignment pattern initializer holds, in each object new constructs, as
// many elements as the pattern's items and each item in its element; a
// replication counts its items as many times as it says. The object's arrays
// were empty.
TEST(ArrayLiteralSim, APatternInitializesADynamicArrayProperty) {
  const char* src =
      "module t;\n"
      "  class P; byte i[] = '{9, 8, 7}; int r[] = '{2{5}}; endclass\n"
      "  P p;\n"
      "  int n, e0, e2, rn, r1;\n"
      "  initial begin\n"
      "    p = new;\n"
      "    n = p.i.size(); e0 = p.i[0]; e2 = p.i[2];\n"
      "    rn = p.r.size(); r1 = p.r[1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "n"), 3u);
  EXPECT_EQ(RunAndGet(src, "e0"), 9u);
  EXPECT_EQ(RunAndGet(src, "e2"), 7u);
  EXPECT_EQ(RunAndGet(src, "rn"), 2u);
  EXPECT_EQ(RunAndGet(src, "r1"), 5u);
}

// §10.9.1 with §7.4.4: a select of a multidimensional array's leading
// dimensions is an unpacked array, which an assignment pattern fills element
// by element: positionally, by `default`, and with nested patterns into the
// subarray of a three-dimensional array, `m3[1]`, and into one of its
// subarrays, `m3[0][1]`. The elements stayed 0.
TEST(ArrayLiteralSim, APatternFillsASubarraySelect) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int mg[2][3];\n"
      "  int m3[2][2][2];\n"
      "  initial begin\n"
      "    mg[1] = '{6, 4, 9};\n"
      "    mg[0] = '{default: 7};\n"
      "    m3[1] = '{'{1, 2}, '{3, 4}};\n"
      "    m3[0][1] = '{5, 6};\n"
      "    $display(\"%p %p\", mg, m3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "'{'{7, 7, 7}, '{6, 4, 9}} '{'{'{0, 0}, '{5, 6}}, '{'{1, 2}, '{3, "
            "4}}}\n");
}

// §10.9.1 with §8.5 and §8.7: a class property may be a multidimensional
// array, which a nested pattern fills one subarray per outer item, through a
// handle, by its bare name in a method and as the initializer of an instance
// or a static property, and which `'{default: 9}` fills at every element. The
// pattern stored nothing through a handle or in a method, and as an initializer
// gave every element the last item, 6.
TEST(ArrayLiteralSim, ANestedPatternFillsAMultidimensionalArrayProperty) {
  SimFixture f;
  auto out = RunCapture(
      "class H;\n"
      "  int g[2][3];\n"
      "  int i[2][3] = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "  static int s[2][2] = '{'{1, 2}, '{3, 4}};\n"
      "  function void fill(); g = '{'{1, 2, 3}, '{4, 5, 6}}; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic H h = new;\n"
      "    automatic H k = new;\n"
      "    automatic H m = new;\n"
      "    h.g = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "    k.fill();\n"
      "    m.g = '{default: 9};\n"
      "    $display(\"%0d %0d %0d %0d\", h.g[0][0], h.g[0][1], h.g[1][0], "
      "h.g[1][2]);\n"
      "    $display(\"%0d %0d %0d %0d\", k.g[0][2], k.g[1][1], h.i[0][0], "
      "h.i[1][2]);\n"
      "    $display(\"%0d %0d %0d %0d\", m.g[0][0], m.g[1][2], H::s[1][0],\n"
      "             H::s[0][1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 4 6\n3 5 1 6\n9 9 3 2\n");
}

// §10.9.1 with §7.4.4 and §8.5: a select of a multidimensional class
// property's leading dimension, `s.g[1]` through a handle or `g[0]` bare in a
// method, is a subarray, which a pattern fills element by element. The pattern
// stored nothing.
TEST(ArrayLiteralSim, APatternFillsASubarrayOfAClassProperty) {
  SimFixture f;
  auto out = RunCapture(
      "class H;\n"
      "  int g[2][3];\n"
      "  function void low(); g[0] = '{4, 5, 6}; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic H s = new;\n"
      "    s.g[1] = '{7, 8, 9};\n"
      "    s.low();\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", s.g[0][0], s.g[0][1], "
      "s.g[0][2], s.g[1][0], s.g[1][1], s.g[1][2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 5 6 7 8 9\n");
}

// §10.9.1 with §11.4.12.1: a pattern whose one item is a concatenation
// replication, `'{ {2{8'h12}} }`, lists one value, 16'h1212, and not the
// replication form `'{2{8'h12}}`, whose items fill a whole dimension. So a
// declaration's one-element array holds 1212, and the inner pattern of a
// two-dimensional one fills its one element with 3434; read as the
// replication form, each held its item alone, 0012 and 0034.
TEST(ArrayLiteralSim, AConcatenationReplicationItemInitializesOneElement) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  logic [15:0] a [1] = '{ {2{8'h12}} };\n"
      "  logic [15:0] m [2][1] = '{ '{ {2{8'h34}} }, '{16'h5678} };\n"
      "  initial $display(\"%h %h %h\", a[0], m[0][0], m[1][0]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1212 3434 5678\n");
}

// §10.9.1 with §11.4.12.1: the same patterns assigned in a procedure give
// the same one value per element.
TEST(ArrayLiteralSim, AConcatenationReplicationItemAssignsOneElement) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  logic [15:0] a [1];\n"
      "  logic [15:0] m [2][1];\n"
      "  initial begin\n"
      "    a = '{ {2{8'h12}} };\n"
      "    m = '{ '{ {2{8'h34}} }, '{16'h5678} };\n"
      "    $display(\"%h %h %h\", a[0], m[0][0], m[1][0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1212 3434 5678\n");
}

// §10.9.1 with §7.5: a dynamic array assigned a pattern of one concatenation
// replication item takes one element, not the two the replication form
// `'{2{8'h12}}` would give it.
TEST(ArrayLiteralSim, AConcatenationReplicationItemSizesADynamicArrayToOne) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class P; logic [15:0] d[]; endclass\n"
      "  P p;\n"
      "  initial begin\n"
      "    p = new;\n"
      "    p.d = '{ {2{8'h12}} };\n"
      "    $display(\"%0d %h\", p.d.size(), p.d[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1212\n");
}

// §11.4.5 with §10.9.1: an array compared with a pattern of one
// concatenation replication item is compared with that one value, so the
// one-element array holding 1212 equals it.
TEST(ArrayLiteralSim, AnArrayEqualsAConcatenationReplicationItem) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  logic [15:0] c [1] = '{16'h1212};\n"
      "  initial $display(\"%0d\", c == '{ {2{8'h12}} });\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

// §10.9.2 with §10.9.1: in the pattern for a structure's unpacked array
// member, a concatenation replication item gives one element, so
// `'{ {2{8'h12}}, 16'h3456 }` fills the two elements of `v[2]`; read as
// three items, it matched no element count.
TEST(ArrayLiteralSim, AConcatenationReplicationItemFillsOneMemberElement) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct { int n; logic [15:0] v[2]; } rec_t;\n"
      "  rec_t r;\n"
      "  initial begin\n"
      "    r = '{5, '{ {2{8'h12}}, 16'h3456 }};\n"
      "    $display(\"%0d %h %h\", r.n, r.v[0], r.v[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 1212 3456\n");
}

// §10.9.1: when more than one type key matches an element, the last one gives
// its value, in an assignment and in a declaration's initializer alike. The
// first was taken.
TEST(ArrayLiteralSim, TheLastOfTwoMatchingTypeKeysGivesTheValue) {
  const char* src =
      "module t;\n"
      "  int d[2] = '{int: 3, int: 7};\n"
      "  int a[2];\n"
      "  int a0, d1;\n"
      "  initial begin a = '{int: 1, int: 2}; a0 = a[0]; d1 = d[1]; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a0"), 2u);
  EXPECT_EQ(RunAndGet(src, "d1"), 7u);
}

// §10.9.1: a default falling on an element that is a structure is applied to
// it member by member, unless the value's own type is that structure, which
// the element is then assigned whole; by an assignment and by a declaration's
// initializer alike. The value was resized to the element's width, giving
// 16'h0001 where each member is 1.
TEST(ArrayLiteralSim, ADefaultFillsAStructureElementMemberByMember) {
  const char* src =
      "typedef struct packed { byte a, b; } s_t;\n"
      "module t;\n"
      "  s_t pv = 16'h1234;\n"
      "  s_t brr[2] = '{default: 1};\n"
      "  s_t arr[2], crr[2];\n"
      "  int a0, b1, c1;\n"
      "  initial begin\n"
      "    arr = '{default: 1};\n"
      "    crr = '{default: pv};\n"
      "    a0 = arr[0]; b1 = brr[1]; c1 = crr[1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a0"), 0x0101u);
  EXPECT_EQ(RunAndGet(src, "b1"), 0x0101u);
  EXPECT_EQ(RunAndGet(src, "c1"), 0x1234u);
}

}  // namespace
