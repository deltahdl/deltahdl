#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AssocArrayAssignment, CopiesEntriesIntKeyed) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[1] = 10;\n"
      "    src[2] = 20;\n"
      "    dst = src;\n"
      "    result = dst[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AssocArrayAssignment, CopiesEntriesStringKeyed) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[string];\n"
      "  int dst[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[\"hello\"] = 42;\n"
      "    dst = src;\n"
      "    result = dst[\"hello\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArrayAssignment, ClearsTargetEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    dst[99] = 999;\n"
      "    dst[100] = 1000;\n"
      "    src[1] = 10;\n"
      "    dst = src;\n"
      "    result = dst.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(AssocArrayAssignment, SourceUnchangedAfterCopy) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[1] = 42;\n"
      "    dst = src;\n"
      "    dst[1] = 100;\n"
      "    result = src[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(AssocArrayAssignment, EmptySourceClearsTarget) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    dst[1] = 10;\n"
      "    dst[2] = 20;\n"
      "    dst = src;\n"
      "    result = dst.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(AssocArrayAssignment, AllEntriesCopied) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[int];\n"
      "  int dst[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    src[1] = 10;\n"
      "    src[2] = 20;\n"
      "    src[3] = 30;\n"
      "    dst = src;\n"
      "    result = dst[1] + dst[2] + dst[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

// §7.9.9 with §8.5: an associative array property is assigned whole like any
// associative array, the target cleared and each source entry copied in,
// whichever side the property stands on: `a.m = x` through a handle takes x's
// two entries and a third after it, `b.m = a.m` copies the three, and `x =
// a.m` makes the module's array those three. With a property on either side
// the assignment did nothing, and the counts read 1, 0 and 2.
TEST(AssocArrayAssignment, PropertyOnEitherSideIsCopiedWhole) {
  auto v = RunAndGet(
      "class P;\n"
      "  int m[int];\n"
      "endclass\n"
      "module t;\n"
      "  int x[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    P a = new, b = new;\n"
      "    x[1] = 5; x[2] = 6;\n"
      "    a.m = x;\n"
      "    a.m[3] = 7;\n"
      "    b.m = a.m;\n"
      "    x = a.m;\n"
      "    result = a.m.num() * 100 + b.m.num() * 10 + x.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 333u);
}

// The same inside a method by the property's bare name, and with class
// handles as the index, as UVM's uvm_phase::add copies `typedef bit
// edges_t[uvm_phase];` sets and then clears the source: the copy keeps the
// two keys the source's delete() then removes from the source alone.
TEST(AssocArrayAssignment, ClassKeyedPropertyCopiedInAMethodOutlivesTheSource) {
  auto v = RunAndGet(
      "class P;\n"
      "  typedef bit edges_t[P];\n"
      "  edges_t succ;\n"
      "  function void take(P o);\n"
      "    succ = o.succ;\n"
      "    o.succ.delete();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    P a = new, b = new, c = new, d = new;\n"
      "    a.succ[b] = 1;\n"
      "    a.succ[c] = 1;\n"
      "    d.take(a);\n"
      "    result = d.succ.num() * 10 + a.succ.num() + d.succ.exists(b) * "
      "100;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 120u);
}

}  // namespace
