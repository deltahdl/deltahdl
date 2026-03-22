#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.7: Function with fixed-size array parameter elaborates.
TEST(ArraySubroutineArgValidation, FuncWithFixedArrayArgElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  function int sum(int a[4]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "endmodule\n"));
}

// §7.7: Task with multiple array parameters elaborates.
TEST(ArraySubroutineArgValidation, TaskWithMultipleArrayArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task copy(input int src[4], output int dst[4]);\n"
             "    dst = src;\n"
             "  endtask\n"
             "endmodule\n"));
}

// §7.7: Function with dynamic array parameter elaborates.
TEST(ArraySubroutineArgValidation, FuncWithDynamicArrayArgElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  function int first(int a[]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "endmodule\n"));
}

// §7.7: Calling function with array actual argument elaborates.
TEST(ArraySubroutineArgValidation, ArrayArgCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[4];\n"
             "  int result;\n"
             "  function int first(int a[4]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(arr);\n"
             "endmodule\n"));
}

// §7.7: Calling function with dynamic array actual elaborates.
TEST(ArraySubroutineArgValidation, DynamicArrayArgCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int result;\n"
             "  function int first(int a[]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(d);\n"
             "endmodule\n"));
}

}  // namespace
