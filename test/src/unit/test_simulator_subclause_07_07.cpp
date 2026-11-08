#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: formal expects 4 elements, "
                            "actual has 3",
                            7, "7.7"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: formal expects 4 elements, "
                            "actual has 2",
                            10, "7.7"));
}

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

TEST(ArrayArgPassing, StringArrayByValueEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  string s[] = '{\"a\", \"bee\", \"c\"};\n"
      "  int result;\n"
      "  function automatic int pick(string a[]);\n"
      "    return (a[0] == \"a\" && a[1] == \"bee\") ? 5 : 0;\n"
      "  endfunction\n"
      "  initial result = pick(s);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

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

TEST(ArrayArgPassing, FixedFormalSizeMismatchNames7_7) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = '{1, 2};\n"
      "  int result;\n"
      "  function int head(int arr[5]);\n"
      "    return arr[0];\n"
      "  endfunction\n"
      "  initial result = head(d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: formal expects", 7, "7.7"));
}

TEST(ArrayArgPassing, FixedActualOfOtherRangePairsLeftToRight) {
  auto v = RunAndGet(
      "module t;\n"
      "  int b[5:2] = '{10, 20, 30, 40};\n"
      "  int result;\n"
      "  function automatic int third(int arr[4:1]);\n"
      "    return arr[2];\n"
      "  endfunction\n"
      "  initial result = third(b);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(ArrayArgPassing, DynamicArrayToRangedFixedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30, 40};\n"
      "  int result;\n"
      "  function automatic int third(int arr[4:1]);\n"
      "    return arr[2];\n"
      "  endfunction\n"
      "  initial result = third(d);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(ArrayArgPassing, QueueToRangedFixedFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  function automatic int third(int arr[4:1]);\n"
      "    return arr[2];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q = {5, 6, 7, 8};\n"
      "    result = third(q);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(ArrayArgPassing, OutputDynamicArrayFormalCopiesBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  function automatic void mk(output int arr[]);\n"
      "    arr = new[3];\n"
      "    arr[2] = 7;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    mk(d);\n"
      "    result = d.size() * 100 + d[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 307u);
}

TEST(ArrayArgPassing, OutputQueueFormalOfTaskCopiesBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  task automatic mkq(output int o[$]);\n"
      "    o.push_back(8);\n"
      "    o.push_back(9);\n"
      "  endtask\n"
      "  initial begin\n"
      "    q = {1, 2, 3};\n"
      "    mkq(q);\n"
      "    result = q.size() * 100 + q[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 209u);
}

TEST(ArrayArgPassing, OutputAssociativeFormalCopiesBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int m[string];\n"
      "  int result;\n"
      "  function automatic void mm(output int a[string]);\n"
      "    a[\"x\"] = 4;\n"
      "    a[\"y\"] = 5;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    m[\"z\"] = 1;\n"
      "    mm(m);\n"
      "    result = m.num() * 100 + m[\"y\"] * 10 + m.exists(\"z\");\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 250u);
}

TEST(ArrayArgPassing, InoutQueueFormalCopiesBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int result;\n"
      "  function automatic void grow(inout int io[$]);\n"
      "    io.push_back(io[0] + io[1]);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    q = {3, 4};\n"
      "    grow(q);\n"
      "    result = q.size() * 100 + q[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 307u);
}

TEST(ArrayArgPassing, OutputFixedFormalToDynamicArrayCopiesBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  function automatic void mf(output int f[2:1]);\n"
      "    f[2] = 6;\n"
      "    f[1] = 5;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    d = new[2];\n"
      "    mf(d);\n"
      "    result = d[0] * 10 + d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 65u);
}

TEST(ArrayArgPassing, OutputFixedFormalOfOtherRangeCopiesBackLeftToRight) {
  auto v = RunAndGet(
      "module t;\n"
      "  int b[5:2];\n"
      "  int result;\n"
      "  function automatic void fill(output int o[4:1]);\n"
      "    o[4] = 1; o[3] = 2; o[2] = 3; o[1] = 4;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    fill(b);\n"
      "    result = b[5] * 1000 + b[4] * 100 + b[3] * 10 + b[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1234u);
}

TEST(ArrayArgPassing, ClassMethodOutputDynamicFormalCopiesBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    function void mk(output int d[]);\n"
      "      d = new[3];\n"
      "      d[1] = 8;\n"
      "    endfunction\n"
      "  endclass\n"
      "  C h;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.mk(d);\n"
      "    result = d.size() * 100 + d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 308u);
}

TEST(ArrayArgPassing, AssociativePropertyThroughHandleToFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int m[string];\n"
      "    function void fill(); m[\"a\"] = 1; m[\"b\"] = 2; endfunction\n"
      "  endclass\n"
      "  function automatic int cnt(int a[string]);\n"
      "    return a.num();\n"
      "  endfunction\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.fill();\n"
      "    result = cnt(h.m);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(ArrayArgPassing, QueuePropertyThroughHandleToFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int q[$];\n"
      "    function void fill(); q.push_back(4); q.push_back(5); endfunction\n"
      "  endclass\n"
      "  function automatic int sum(int a[]);\n"
      "    int s = 0;\n"
      "    foreach (a[i]) s += a[i];\n"
      "    return s;\n"
      "  endfunction\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.fill();\n"
      "    result = sum(h.q);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(ArrayArgPassing, FixedPropertyThroughHandleToFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int r[4:1];\n"
      "    function void fill(); r[4] = 1; r[3] = 2; r[2] = 3; r[1] = 4; "
      "endfunction\n"
      "  endclass\n"
      "  function automatic int third(int a[1:4]);\n"
      "    return a[3];\n"
      "  endfunction\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.fill();\n"
      "    result = third(h.r);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(ArrayArgPassing, OutputDynamicFormalToDynamicPropertyCopiesBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int d[];\n"
      "  endclass\n"
      "  function automatic void mk(output int a[]);\n"
      "    a = new[2];\n"
      "    a[1] = 5;\n"
      "  endfunction\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    mk(h.d);\n"
      "    result = h.d.size() * 100 + h.d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 205u);
}

TEST(ArrayArgPassing, BarePropertyActualInMethodCopiesBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    int f[3];\n"
      "    function void go(); fill3(f); endfunction\n"
      "    function int total(); return sum3(f); endfunction\n"
      "  endclass\n"
      "  function automatic void fill3(output int a[3]);\n"
      "    a[0] = 9; a[1] = 8; a[2] = 7;\n"
      "  endfunction\n"
      "  function automatic int sum3(int a[3]);\n"
      "    return a[0] * 100 + a[1] * 10 + a[2];\n"
      "  endfunction\n"
      "  C h;\n"
      "  int result;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.go();\n"
      "    result = h.total();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 987u);
}

TEST(ArrayArgPassing, TwoDimFixedActualReachesFunctionFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int b[2][3];\n"
      "  int result;\n"
      "  function automatic int g(int a[2][3]);\n"
      "    return a[1][2] * 10 + a[0][1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    b[1][2] = 7; b[0][1] = 4;\n"
      "    result = g(b);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 74u);
}

TEST(ArrayArgPassing, TwoDimActualOfOtherRangesPairsByPosition) {
  auto v = RunAndGet(
      "module t;\n"
      "  int b[1:3][0:2];\n"
      "  int result;\n"
      "  task automatic fun(int a[3:1][3:1]);\n"
      "    result = a[2][3] * 10 + a[1][1];\n"
      "  endtask\n"
      "  initial begin\n"
      "    b[2][0] = 7; b[3][2] = 5;\n"
      "    fun(b);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 75u);
}

TEST(ArrayArgPassing, TwoDimOutputFormalCopiedBackByPosition) {
  auto v = RunAndGet(
      "module t;\n"
      "  int b[1:3][1:3];\n"
      "  int result;\n"
      "  task automatic fill(output int a[3:1][3:1]);\n"
      "    a[2][3] = 7; a[1][1] = 5;\n"
      "  endtask\n"
      "  initial begin\n"
      "    fill(b);\n"
      "    result = b[2][1] * 10 + b[3][3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 75u);
}

TEST(ArrayArgPassing, TwoDimInoutFormalCopiedInAndBack) {
  auto v = RunAndGet(
      "module t;\n"
      "  int c[2][2];\n"
      "  int result;\n"
      "  task automatic inc(inout int a[2][2]);\n"
      "    a[1][0] = a[1][0] + 1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    c[1][0] = 8;\n"
      "    inc(c);\n"
      "    result = c[1][0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

TEST(ArrayArgPassing, DynamicOfDynamicActualReachesTwoDimFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[][];\n"
      "  int result;\n"
      "  function automatic int dd(int a[3:1][3:1]);\n"
      "    return a[2][3] * 10 + a[1][1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    d = new[3];\n"
      "    foreach (d[i]) d[i] = new[3];\n"
      "    d[1][0] = 9; d[2][2] = 6;\n"
      "    result = dd(d);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 96u);
}

TEST(ArrayArgPassing, DynamicOfDynamicInnerSizeMismatchRuntimeError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[][];\n"
      "  int result;\n"
      "  function automatic int dd(int a[3:1][3:1]);\n"
      "    return a[2][3];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    d = new[3];\n"
      "    foreach (d[i]) d[i] = new[3];\n"
      "    d[1] = new[2];\n"
      "    result = dd(d);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "array size mismatch: formal expects 3 elements "
                            "in dimension 2, actual has 2",
                            11, "7.7"));
}

TEST(ArrayArgPassing, StringMethodOnElementOfStringArrayFormal) {
  auto v = RunAndGet(
      "module t;\n"
      "  string ss[5:2];\n"
      "  int result;\n"
      "  function automatic int f(string a[4:1]);\n"
      "    return a[4].len() * 10 + a[1].len();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    ss[5] = \"abc\"; ss[2] = \"z\";\n"
      "    result = f(ss);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 31u);
}

}  // namespace
