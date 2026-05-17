#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ArraySubroutineArgValidation, FuncWithFixedArrayArgElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  function int sum(int a[4]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, TaskWithMultipleArrayArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task copy(input int src[4], output int dst[4]);\n"
             "    dst = src;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(ArraySubroutineArgValidation, FuncWithDynamicArrayArgElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  function int first(int a[]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "endmodule\n"));
}

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

}
