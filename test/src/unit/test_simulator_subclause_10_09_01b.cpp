#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

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

// §10.9.1 with Syntax 10-5: a type key may be a typedef name, which sets each
// element of a matching type -- an array declared with the typedef or with the
// type it names -- in an assignment and a declaration's initializer alike. The
// name was evaluated as an index, so at most one element took the value.
TEST(ArrayLiteralSim, ATypedefKeySetsTheElementsOfItsType) {
  const char* src =
      "typedef logic [7:0] byte_t;\n"
      "module t;\n"
      "  byte_t arr[3];\n"
      "  byte_t ini[2] = '{byte_t: 8'h5};\n"
      "  logic [7:0] la[2];\n"
      "  int a0, a2, i1, l1;\n"
      "  initial begin\n"
      "    arr = '{byte_t: 8'h1};\n"
      "    la = '{byte_t: 8'h7};\n"
      "    a0 = arr[0]; a2 = arr[2]; i1 = ini[1]; l1 = la[1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a0"), 1u);
  EXPECT_EQ(RunAndGet(src, "a2"), 1u);
  EXPECT_EQ(RunAndGet(src, "i1"), 5u);
  EXPECT_EQ(RunAndGet(src, "l1"), 7u);
}

// §10.9.1 with §6.22.1: a type key sets the elements whose type matches its
// own. The one-bit `logic` matches no `logic [7:0]` element; `int` matches a
// `bit signed [31:0]` element, of its state, signing and range, and no
// `bit [31:0]` one, which is unsigned. Matched by kind, `logic:` set the
// vector and `int:` neither bit vector.
TEST(ArrayLiteralSim, ATypeKeyMatchesAnElementOfItsFullType) {
  const char* src =
      "module t;\n"
      "  logic [7:0] lv[2];\n"
      "  bit signed [31:0] bs[2] = '{int: 5, default: 0};\n"
      "  bit [31:0] bu[2];\n"
      "  int l0, s1, u1;\n"
      "  initial begin\n"
      "    lv = '{logic: 8'hCD, default: 8'h0};\n"
      "    bu = '{int: 5, default: 0};\n"
      "    l0 = lv[0]; s1 = bs[1]; u1 = bu[1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "l0"), 0u);
  EXPECT_EQ(RunAndGet(src, "s1"), 5u);
  EXPECT_EQ(RunAndGet(src, "u1"), 0u);
}

// §10.9.1 with §6.22.1: two vector types match only over the same packed
// bounds, so a `logic [7:0]` typedef key sets no `logic [8:1]` element, eight
// bits wide as it is, in an assignment, a declaration's initializer or a
// multidimensional array's; the default gives each 0.
TEST(ArrayLiteralSim, ATypeKeyMatchesOnlyAnElementOfItsPackedBounds) {
  const char* src =
      "typedef logic [7:0] byte_t;\n"
      "module t;\n"
      "  logic [8:1] ra[2];\n"
      "  logic [8:1] ri[2] = '{byte_t: 8'h1, default: 8'h0};\n"
      "  logic [8:1] rm[2][2] = '{byte_t: 8'h1, default: 8'h0};\n"
      "  logic [7:0] rk[2][2] = '{byte_t: 8'h1, default: 8'h0};\n"
      "  int a1, i1, m11, k11;\n"
      "  initial begin\n"
      "    ra = '{byte_t: 8'h1, default: 8'h0};\n"
      "    a1 = ra[1]; i1 = ri[1]; m11 = rm[1][1]; k11 = rk[1][1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a1"), 0u);
  EXPECT_EQ(RunAndGet(src, "i1"), 0u);
  EXPECT_EQ(RunAndGet(src, "m11"), 0u);
  EXPECT_EQ(RunAndGet(src, "k11"), 1u);
}

// §10.9.1: a type key that matches no element of an array of structures is
// applied to each element's members by §10.9.2's rules, in an assignment and
// a declaration's initializer alike. It was asked of the elements alone, so
// the members kept no value.
TEST(ArrayLiteralSim, ATypeKeyReachesTheMembersOfStructureElements) {
  const char* src =
      "typedef struct packed { int x, y; } s_t;\n"
      "module t;\n"
      "  s_t arr[2];\n"
      "  s_t ini[2] = '{int: 4};\n"
      "  int x0, y1, iy0;\n"
      "  initial begin\n"
      "    arr = '{int: 7};\n"
      "    x0 = arr[0].x; y1 = arr[1].y; iy0 = ini[0].y;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "x0"), 7u);
  EXPECT_EQ(RunAndGet(src, "y1"), 7u);
  EXPECT_EQ(RunAndGet(src, "iy0"), 4u);
}

// §10.9.1 with §6.22.1: an array a block declares takes a type key by its
// element type as a module's does -- an int element by int's signing and
// range, and an element written with a typedef by the typedef's.
TEST(ArrayLiteralSim, ABlockArrayTakesATypeKeyOfItsElementType) {
  const char* src =
      "typedef logic [7:0] byte_t;\n"
      "module t;\n"
      "  int i1, b0;\n"
      "  initial begin\n"
      "    int ia[2];\n"
      "    byte_t ba[2];\n"
      "    ia = '{int: 4};\n"
      "    ba = '{logic: 8'h1, default: 8'h9};\n"
      "    i1 = ia[1]; b0 = ba[0];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "i1"), 4u);
  EXPECT_EQ(RunAndGet(src, "b0"), 9u);
}

// §10.9.1: an item standing at a dimension of a multidimensional array other
// than its last is assigned to that dimension's subarray, so an item of the
// subarray's unpacked array type -- a typed pattern, keyed or positional, or a
// variable of that type -- gives the subarray its elements in order, whether it
// is positional, index-keyed or the default. Each row read one scalar instead,
// the same value at all three leaves.
TEST(ArrayLiteralSim, AnUnpackedArrayItemFillsItsSubarrayElementForElement) {
  SimFixture f;
  auto out = RunCapture(
      "typedef int row_t [3];\n"
      "module t;\n"
      "  int a [2][3];\n"
      "  int b [2][3];\n"
      "  int c [2][3];\n"
      "  int d [2][3];\n"
      "  row_t r = '{1, 2, 3};\n"
      "  initial begin\n"
      "    a = '{default: row_t'{4, 5, 6}};\n"
      "    b = '{default: r};\n"
      "    c = '{0: r, default: '{7, 8, 9}};\n"
      "    d = '{r, row_t'{default: 5}};\n"
      "    $display(\"%p %p\", a, b);\n"
      "    $display(\"%p %p\", c, d);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "'{'{4, 5, 6}, '{4, 5, 6}} '{'{1, 2, 3}, '{1, 2, 3}}\n"
            "'{'{1, 2, 3}, '{7, 8, 9}} '{'{1, 2, 3}, '{5, 5, 5}}\n");
}

// §10.9.1 with §7.4.4, §7.4.5 and §7.6: a slice, a select of another array's
// leading dimension and a queue are unpacked arrays too, so each fills the
// subarray it stands for, its elements paired with the subarray's by their
// left-to-right position: `e [1:0][2:0]` takes 7 at e[1][2] from g[0][0].
TEST(ArrayLiteralSim, ASliceASubarraySelectAndAQueueFillTheirSubarrays) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int src [6];\n"
      "  int g [2][3];\n"
      "  int a [2][3];\n"
      "  int b [2][3];\n"
      "  int e [1:0][2:0];\n"
      "  int q [$];\n"
      "  initial begin\n"
      "    src = '{1, 2, 3, 4, 5, 6};\n"
      "    g = '{'{7, 8, 9}, '{10, 11, 12}};\n"
      "    q = {13, 14, 15};\n"
      "    a = '{src[0:2], src[3:5]};\n"
      "    b = '{g[1], q};\n"
      "    e = '{g[0], g[1]};\n"
      "    $display(\"%p %p\", a, b);\n"
      "    $display(\"%0d %0d %0d\", e[1][2], e[1][0], e[0][2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "'{'{1, 2, 3}, '{4, 5, 6}} '{'{10, 11, 12}, '{13, 14, 15}}\n"
            "7 9 10\n");
}

// §10.9.1: an item of a non-aggregate type is applied recursively to every
// element of the subarray it stands for, and a select of one element of an
// array is such an item, not an array.
TEST(ArrayLiteralSim, AnElementSelectItemFillsEveryLeafOfItsSubarray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int src [3];\n"
      "  int a [2][3];\n"
      "  initial begin\n"
      "    src = '{1, 2, 3};\n"
      "    a = '{default: src[1]};\n"
      "    $display(\"%p\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{'{2, 2, 2}, '{2, 2, 2}}\n");
}

// §10.9.1 with §7.6: a queue standing for a subarray is assigned to it as one
// unpacked array to another, which needs as many elements as the subarray
// holds, and a queue's size is only known as the assignment runs.
TEST(ArrayLiteralSim, AQueueItemOfTheWrongSizeIsARuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q [$];\n"
      "  int a [2][3];\n"
      "  initial begin\n"
      "    q = {1, 2};\n"
      "    a = '{default: q};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array size mismatch in assignment to fixed-size array", 6, "7.6"));
}

// §10.9.1: a declaration's initializer follows the array's dimensions as an
// assignment does, so an item of the subarray's unpacked array type standing
// at the first dimension -- a typed pattern, keyed or positional, or a
// variable of that type -- gives the subarray its elements in order. Each row
// read one scalar instead, the same value at all three leaves.
TEST(ArrayLiteralSim, ADeclarationsUnpackedArrayItemFillsItsSubarray) {
  SimFixture f;
  auto out = RunCapture(
      "typedef int row_t [3];\n"
      "module t;\n"
      "  row_t r = '{1, 2, 3};\n"
      "  int a [2][3] = '{default: row_t'{4, 5, 6}};\n"
      "  int b [2][3] = '{default: r};\n"
      "  int c [2][3] = '{0: r, default: '{7, 8, 9}};\n"
      "  int d [2][3] = '{r, row_t'{default: 5}};\n"
      "  initial begin\n"
      "    $display(\"%p %p\", a, b);\n"
      "    $display(\"%p %p\", c, d);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "'{'{4, 5, 6}, '{4, 5, 6}} '{'{1, 2, 3}, '{1, 2, 3}}\n"
            "'{'{1, 2, 3}, '{7, 8, 9}} '{'{1, 2, 3}, '{5, 5, 5}}\n");
}

// §10.9.1 with §7.4.4 and §7.6: in a declaration's initializer too, a slice
// and a select of another array's leading dimension fill the subarray they
// stand for by left-to-right position, which in `e [1:0][2:0]` puts g[0][0]'s
// 7 at e[1][2]; an element select is no array and reaches every leaf.
TEST(ArrayLiteralSim, ADeclarationsSliceAndSubarraySelectFillTheirSubarrays) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int src [6] = '{1, 2, 3, 4, 5, 6};\n"
      "  int g [2][3] = '{'{7, 8, 9}, '{10, 11, 12}};\n"
      "  int a [2][3] = '{src[0:2], src[3:5]};\n"
      "  int b [2][3] = '{g[1], g[0]};\n"
      "  int e [1:0][2:0] = '{g[0], g[1]};\n"
      "  int s [2][3] = '{default: src[1]};\n"
      "  initial begin\n"
      "    $display(\"%p %p %p\", a, b, s);\n"
      "    $display(\"%0d %0d %0d\", e[1][2], e[1][0], e[0][2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "'{'{1, 2, 3}, '{4, 5, 6}} '{'{10, 11, 12}, '{7, 8, 9}} "
            "'{'{2, 2, 2}, '{2, 2, 2}}\n"
            "7 9 10\n");
}

// §10.9.1 with §7.6: a queue standing for a subarray in a declaration's
// initializer is assigned to it as one unpacked array to another, which needs
// as many elements as the subarray holds; a queue's size is only known as the
// initializer is evaluated.
TEST(ArrayLiteralSim, ADeclarationsQueueItemOfTheWrongSizeIsAnError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q [$];\n"
      "  int a [2][3] = '{default: q};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "array size mismatch in assignment to fixed-size array", 3, "7.6"));
}

// §10.9.1 assigns each item of a declaration's array pattern to its element
// by the element type's assignment rules, and §6.12 with §6.12.1 makes that a
// conversion to the element's real format: single precision for a shortreal,
// and an integer item converted by its value. The shortreal elements held
// the low 32 bits of each item's double, 0.0 for both 1.0 and 2.5 (#7489),
// and an integer item kept its integer bits in a real or shortreal element.
TEST(ArrayLiteralSim, ADeclarationsPatternGivesRealElementsTheirValues) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  shortreal s [2] = '{1.0, 2.5};\n"
      "  shortreal i [2] = '{3, -2};\n"
      "  shortreal k [2] = '{1: 0.5, default: -4.0};\n"
      "  real r [2] = '{1.0, 2.5};\n"
      "  real j [2] = '{3, -2};\n"
      "  initial begin\n"
      "    $display(\"%0.1f %0.1f %0.1f %0.1f %0.1f %0.1f\",\n"
      "             s[0], s[1], i[0], i[1], k[0], k[1]);\n"
      "    $display(\"%0.1f %0.1f %0.1f %0.1f\", r[0], r[1], j[0], j[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "1.0 2.5 3.0 -2.0 -4.0 0.5\n"
            "1.0 2.5 3.0 -2.0\n");
}

// §10.9.1 with §7.4.4: the leaves of a multidimensional shortreal array take
// the single-precision values of the items that reach them, as a
// one-dimensional array's elements do.
TEST(ArrayLiteralSim, ADeclarationsPatternGivesShortrealLeavesTheirValues) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  shortreal m [2][2] = '{'{1.0, 2.5}, '{-4.0, 7}};\n"
      "  initial $display(\"%0.1f %0.1f %0.1f %0.1f\",\n"
      "                   m[0][0], m[0][1], m[1][0], m[1][1]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1.0 2.5 -4.0 7.0\n");
}

}  // namespace
