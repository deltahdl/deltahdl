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

}  // namespace
