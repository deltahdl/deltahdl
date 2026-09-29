#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DynamicArraySimulation, DeclWithInitHasElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30};\n"
      "  int result;\n"
      "  initial result = d[1];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArraySimulation, DefaultUninitializedSizeZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArraySimulation, DeclWithInitCorrectSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{5, 6, 7, 8};\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

// §7.5: a dynamic array admits any variable data type as its element. Build a
// dynamic array of a packed-vector element type from real source and read an
// element back at run time to observe the non-int element type in effect.
TEST(DynamicArraySimulation, PackedVectorElementHoldsValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] d[] = '{8'hA1, 8'hB2, 8'hC3};\n"
      "  int result;\n"
      "  initial result = d[2];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xC3u);
}

// §7.5 (printed pages 157-158 of the LRM): a declaration whose first unpacked
// dimension is `[]` declares a dynamic array wherever it stands, sized by the
// new[] constructor (§7.5.1) and read by size() (§7.5.2). Declared in an
// initial block, `int d[]` built no storage -- CreateBlockArrayElements in
// statement_assign_decl.cpp read no bounds off the dimension -- so `d =
// new[3]` sized nothing, `d[1] = 5` wrote nothing and `d[1] + d.size()`
// read 0 where the module-scope declaration reads 8.
TEST(DynamicArraySimulation, BlockDeclaredDynamicArraySizedByNewHoldsElements) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    int d[];\n"
                      "    d = new[3];\n"
                      "    d[1] = 5;\n"
                      "    y = d[1] + d.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            8u);
}

// §10.7 (printed page 258) with §7.5: an assignment to an element of a
// dynamic array takes the element's width, so `d[0] = 1` on `byte d[]`
// leaves an 8-bit element, `$bits(d[0])` reading 8 as it does before the
// write, and `d[1] = 300` holds 300's low byte, 44. The element store kept
// the right-hand value's own width, the 32-bit literal, so
// `{<< 8 {..., d}}` streamed four bytes for the element and the suite's
// 11.4.14.4--dynamic_array_stream-sim.sv packed 32 bytes where 17 were
// written (#4365). y reads 8 * 1000 + 44.
TEST(DynamicArraySimulation, ElementWriteTakesTheElementWidth) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    byte d[];\n"
                      "    d = new[2];\n"
                      "    d[0] = 1;\n"
                      "    d[1] = 300;\n"
                      "    y = $bits(d[0]) * 1000 + d[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            8044u);
}

// The same declaration as a function body's local, which CreateFuncLocalVar
// (eval_function_body.cpp) creates and the same aggregate builder backs.
TEST(DynamicArraySimulation, FunctionBodyDynamicArraySizedByNewHoldsElements) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  function int f();\n"
                      "    int d[];\n"
                      "    d = new[3];\n"
                      "    d[1] = 5;\n"
                      "    return d[1] + d.size();\n"
                      "  endfunction\n"
                      "  int y;\n"
                      "  initial y = f();\n"
                      "endmodule\n",
                      "y"),
            8u);
}

// §7.5.1 (printed page 158 of the LRM): the new[] constructor may stand as
// the right-hand side of a variable declaration assignment, sizing the
// array. A block's `int d[] = new[3]` was evaluated onto the carrier variable
// and sized nothing (InitializeDeclVariable in statement_assign_decl.cpp),
// where the module's declaration is sized by LowerDynArrayNewInit, so
// `d.size()` read 0 for 3.
TEST(DynamicArraySimulation,
     BlockDeclaredDynamicArraySizedByItsNewInitializer) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static int d[] = new[3];\n"
                      "    y = d.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            3u);
}

// The same initializer on a function body's local, and §7.5.1's optional
// initialization array: `int e[] = new[4](d)` takes d's three elements and
// a fourth at the element type's default, so e.size() * 100 + e[1] + e[3]
// reads 405 from d's `d[1] = 5`. A local sized by nothing read 0.
TEST(DynamicArraySimulation, FunctionBodyDynamicArraySizedByItsNewInitializer) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  function int f();\n"
                      "    static int d[] = new[3];\n"
                      "    int e[];\n"
                      "    d[1] = 5;\n"
                      "    e = new[4](d);\n"
                      "    return e.size() * 100 + e[1] + e[3];\n"
                      "  endfunction\n"
                      "  int y;\n"
                      "  initial y = f();\n"
                      "endmodule\n",
                      "y"),
            405u);
}

// §7.5 with §7.2: each element of a dynamic array of structures is a
// structure, so `md[1].f1` reads the member of the element `md[1] = e`
// stored -- for a module variable, a block local and a subroutine's `input T
// a[]` formal alike. Built into a name, `md[1]` named no variable and read 0.
TEST(DynamicArraySim, MemberOfAStructElement) {
  const char* src =
      "module t;\n"
      "  typedef struct { int f1; bit f2; } T;\n"
      "  T md[];\n"
      "  int mod, loc, fn;\n"
      "  function automatic int g(input T a[]);\n"
      "    return a[1].f1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    T ld[];\n"
      "    T e;\n"
      "    md = new[2];\n"
      "    ld = new[2];\n"
      "    e.f1 = 9;\n"
      "    e.f2 = 1;\n"
      "    md[1] = e;\n"
      "    ld[1] = e;\n"
      "    mod = md[1].f1;\n"
      "    loc = ld[1].f1;\n"
      "    fn = g(md);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "mod"), 9u);
  EXPECT_EQ(RunAndGet(src, "loc"), 9u);
  EXPECT_EQ(RunAndGet(src, "fn"), 9u);
}

// §7.5 with §8.4 and §8.5: a dynamic array property of a class type is sized
// by new[] -- in a method and through a handle alike -- and each element is a
// handle whose object's property an element select reaches.
TEST(DynamicArraySim, PropertyOfClassHandlesSizedByNew) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Item;\n"
      "    int id;\n"
      "    function new(int i); id = i; endfunction\n"
      "  endclass\n"
      "  class Holder;\n"
      "    Item items[];\n"
      "    function void fill(int n); items = new[n];\n"
      "      foreach (items[i]) items[i] = new(10 + i); endfunction\n"
      "    function int total(); int s = 0; foreach (items[i]) s += "
      "items[i].id;\n"
      "      return s; endfunction\n"
      "  endclass\n"
      "  Holder h, g;\n"
      "  initial begin\n"
      "    h = new; h.fill(3); g = new;\n"
      "    g.items = new[2]; g.items[1] = new(5);\n"
      "    $display(\"%0d %0d %0d %0d\", h.items[2].id, h.total(),\n"
      "             g.items.size(), g.items[1].id);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "12 33 2 5\n");
}

}  // namespace
