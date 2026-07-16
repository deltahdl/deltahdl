#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ArrayArgPassing, PassByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[4];\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = 10; a[1] = 20; a[2] = 30; a[3] = 40;\n"
      "    result = second(a);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(ArrayArgPassing, CopySemanticsEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[3];\n"
      "  int result;\n"
      "  function int modify(int arr[3]);\n"
      "    arr[0] = 999;\n"
      "    return arr[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = 5; a[1] = 10; a[2] = 15;\n"
      "    result = modify(a);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 999u);
}

TEST(ArrayArgPassing, CallerUnchangedEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[2];\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function int modify(int arr[2]);\n"
      "    arr[0] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = 42; a[1] = 7;\n"
      "    dummy = modify(a);\n"
      "    result = a[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// A fixed-size formal may also receive a dynamic array of equal size. The
// elements are copied in by value and read back through the formal.
TEST(ArrayArgPassing, DynamicArrayEqualSizeToFixedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30, 40};\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial result = second(d);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// Passing a dynamic array whose size differs from a fixed-size formal is the
// case the standard flags as requiring a run-time check: the mismatch is
// diagnosed when the call is bound.
TEST(ArrayArgPassing, DynamicArraySizeMismatchToFixedFormalRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = '{10, 20, 30};\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial result = second(d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
}

// The same equal-size run-time check governs a queue actual bound to a
// fixed-size formal.
TEST(ArrayArgPassing, QueueSizeMismatchToFixedFormalRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    result = second(q);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
}

// An unsized formal dimension matches any size of the actual, so a formal that
// accepts a dynamic array can be passed a fixed-size array of compatible type.
TEST(ArrayArgPassing, FixedArrayToUnsizedDynamicFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[4];\n"
      "  int result;\n"
      "  function int third(int arr[]);\n"
      "    return arr[2];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = 5; a[1] = 10; a[2] = 30; a[3] = 40;\n"
      "    result = third(a);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// A dynamic array bound to an unsized formal is copied by value through the
// queue-backed representation, so the callee reads the actual's elements.
TEST(ArrayArgPassing, DynamicArrayToUnsizedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30, 40};\n"
      "  int result;\n"
      "  function int third(int arr[]);\n"
      "    return arr[2];\n"
      "  endfunction\n"
      "  initial result = third(d);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// A queue of equal size binds to a fixed-size formal: its elements are copied
// in by value and read back through the formal.
TEST(ArrayArgPassing, QueueEqualSizeToFixedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  function int second(int arr[4]);\n"
      "    return arr[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    q.push_back(30);\n"
      "    q.push_back(40);\n"
      "    result = second(q);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// A queue bound to an unsized formal is copied by value into the formal's own
// queue-backed storage, so the callee reads the actual's elements.
TEST(ArrayArgPassing, QueueToUnsizedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  function int third(int arr[]);\n"
      "    return arr[2];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    q.push_back(30);\n"
      "    q.push_back(40);\n"
      "    result = third(q);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

// §7.7 lists associative arrays among the array types passed by value: binding
// an associative-array actual copies its entries into the formal, so the callee
// reads back through the formal the value the caller stored under a given key.
// Exercises the associative branch of the real argument-binding path.
TEST(ArrayArgPassing, AssociativeArrayByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  function automatic int lookup(int a[int]);\n"
      "    return a[7];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[3] = 11; aa[7] = 22;\n"
      "    result = lookup(aa);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 22u);
}

// §7.7: the associative-array actual is passed as a copy, so mutating the
// formal inside the callee leaves the caller's associative array untouched --
// the same copy-by-value guarantee the fixed/dynamic/queue cases above observe,
// now for the associative array type the subclause also enumerates.
TEST(ArrayArgPassing, AssociativeArrayCallerUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function automatic int clobber(int a[int]);\n"
      "    a[7] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    aa[7] = 22;\n"
      "    dummy = clobber(aa);\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 22u);
}

// Because the bind makes an independent copy, mutating the formal inside the
// callee leaves the caller's dynamic array untouched.
TEST(ArrayArgPassing, DynamicArrayCallerUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{42, 7, 3};\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function int modify(int arr[3]);\n"
      "    arr[0] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    dummy = modify(d);\n"
      "    result = d[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.7 lists strings among the element types an array argument may carry (its
// own example uses `string arr[...]`). A string element takes a distinct,
// non-integral storage path, so passing a string array by value must copy those
// elements into the formal; the callee then reads back the value the caller
// stored. Built from a real `'{...}` string-array initializer and driven
// through the full pipeline.
TEST(ArrayArgPassing, StringArrayByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s[] = '{\"a\", \"bee\", \"c\"};\n"
      "  int result;\n"
      "  function automatic int pick(string a[]);\n"
      "    return (a[1] == \"bee\") ? 5 : 0;\n"
      "  endfunction\n"
      "  initial result = pick(s);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

// §7.7: the copy-by-value guarantee holds for the queue array type too --
// mutating the formal inside the callee leaves the caller's queue untouched,
// mirroring the fixed/dynamic/associative caller-unchanged cases for the
// remaining array type.
TEST(ArrayArgPassing, QueueCallerUnchanged) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int dummy;\n"
      "  int result;\n"
      "  function automatic int modify(int arr[]);\n"
      "    arr[0] = 999;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q.push_back(42);\n"
      "    q.push_back(7);\n"
      "    dummy = modify(q);\n"
      "    result = q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// §7.7: a subroutine is a task or a function; array arguments are passed by
// value to either. The prior cases all call functions, so this exercises the
// task syntactic position -- a fixed array copied into a task's input formal,
// with the selected element handed back through an output formal and observed.
TEST(ArrayArgPassing, ArrayArgToTaskEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[3];\n"
      "  int result;\n"
      "  task automatic grab(input int arr[3], output int o);\n"
      "    o = arr[2];\n"
      "  endtask\n"
      "  initial begin\n"
      "    a[0] = 1; a[1] = 2; a[2] = 33;\n"
      "    grab(a, result);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 33u);
}

}  // namespace
