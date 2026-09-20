#include <gtest/gtest.h>

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
                      "    int d[] = new[3];\n"
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
                      "    int d[] = new[3];\n"
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

}  // namespace
