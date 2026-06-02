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

// A dynamic array may be bound to a fixed-size formal: the equal-size
// requirement is checked at run time, so elaboration accepts the association.
TEST(ArraySubroutineArgValidation, DynamicActualToFixedFormalCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int d[];\n"
             "  int result;\n"
             "  function int first(int a[4]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(d);\n"
             "endmodule\n"));
}

// A formal that accepts a dynamic array may be passed a fixed-size array of a
// compatible type; elaboration accepts the association.
TEST(ArraySubroutineArgValidation, FixedActualToDynamicFormalCallElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr[4];\n"
             "  int result;\n"
             "  function int first(int a[]);\n"
             "    return a[0];\n"
             "  endfunction\n"
             "  initial result = first(arr);\n"
             "endmodule\n"));
}

// A dynamic array passed to a DPI import's open-array (unsized) output formal
// is illegal: the unsized dimension leaves the C side no fixed element count to
// write back into.
TEST(ArraySubroutineArgValidation, DpiOpenArrayOutputRejectsDynamicArray) {
  EXPECT_FALSE(
      ElabOk("module t;\n"
             "  import \"DPI-C\" function void f(output int a[]);\n"
             "  int dyn[];\n"
             "  initial f(dyn);\n"
             "endmodule\n"));
}

// A queue is rejected for the same open-array output formal.
TEST(ArraySubroutineArgValidation, DpiOpenArrayOutputRejectsQueue) {
  EXPECT_FALSE(
      ElabOk("module t;\n"
             "  import \"DPI-C\" function void f(output int a[]);\n"
             "  int q[$];\n"
             "  initial f(q);\n"
             "endmodule\n"));
}

// The prohibition is specific to the output direction: a dynamic array is a
// legal actual for an open-array input formal.
TEST(ArraySubroutineArgValidation, DpiOpenArrayInputAcceptsDynamicArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  import \"DPI-C\" function void f(input int a[]);\n"
             "  int dyn[];\n"
             "  initial f(dyn);\n"
             "endmodule\n"));
}

// A fixed-size array remains a legal actual for an open-array output formal;
// only dynamic arrays and queues are prohibited.
TEST(ArraySubroutineArgValidation, DpiOpenArrayOutputAcceptsFixedArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  import \"DPI-C\" function void f(output int a[]);\n"
             "  int fixed[4];\n"
             "  initial f(fixed);\n"
             "endmodule\n"));
}

}
