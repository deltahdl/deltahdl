#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(MultidimensionalArraySimulation, PackedAndUnpackedDims) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "  int result;\n"
      "  initial begin\n"
      "    joe[1] = 32'hDEADBEEF;\n"
      "    result = joe[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xDEADBEEFu);
}

TEST(MultidimensionalArraySimulation, DistinctUnpackedElementsAreIndependent) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "  int result;\n"
      "  initial begin\n"
      "    joe[1] = 32'h11111111;\n"
      "    joe[2] = 32'h22222222;\n"
      "    result = joe[2] - joe[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x11111111u);
}

TEST(MultidimensionalArraySimulation, PackedElementParticipatesInArithmetic) {
  auto v = RunAndGet(
      "module t;\n"
      "  bit [3:0] [7:0] joe [1:10];\n"
      "  int result;\n"
      "  initial begin\n"
      "    joe[8] = 32'h0000000F;\n"
      "    joe[9] = joe[8] + 1;\n"
      "    result = joe[9];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 16u);
}

TEST(MultidimensionalArraySimulation, PackedDimsViaTypedefStagingWidthHonored) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit [1:5] bsix;\n"
      "  bsix [1:10] v5;\n"
      "  logic [63:0] result;\n"
      "  initial begin\n"
      "    v5 = '1;\n"
      "    result = v5;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x0003FFFFFFFFFFFFull);
}

TEST(MultidimensionalArraySimulation,
     UnpackedDimsViaTypedefStagingAddressable) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit [1:5] bsix;\n"
      "  typedef bsix mem_type [0:3];\n"
      "  mem_type ba [0:7];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem_type bb [0:1];\n"
      "    ba[0][0] = 5'd7;\n"
      "    ba[7][3] = 5'd9;\n"
      "    ba[0][3] = 5'd1;\n"
      "    bb[1][2] = 5'd4;\n"
      "    result = ba[0][0] + ba[7][3] + ba[0][3] + bb[1][2] + bb[1][0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 21u);
}

TEST(MultidimensionalArraySimulation,
     ThreeUnpackedDimsIndexIndependentElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int A[2][3][4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    A[0][0][0] = 100;\n"
      "    A[1][2][3] = 20;\n"
      "    A[0][2][1] = 3;\n"
      "    result = A[0][0][0] + A[1][2][3] + A[0][2][1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 123u);
}

TEST(MultidimensionalArraySimulation, NonblockingReachesSameElementAsBlocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A[2][3];\n"
      "  initial begin\n"
      "    A[0][0] = 7;\n"
      "    A[1][2] <= 9;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* written_blocking = f.ctx.FindVariable("A[0][0]");
  auto* written_nonblocking = f.ctx.FindVariable("A[1][2]");
  ASSERT_NE(written_blocking, nullptr);
  ASSERT_NE(written_nonblocking, nullptr);
  EXPECT_EQ(written_blocking->value.ToUint64(), 7u);
  EXPECT_EQ(written_nonblocking->value.ToUint64(), 9u);
}

TEST(MultidimensionalArraySimulation, SubarrayCopyElementsGetTheirOwnWords) {
  SimFixture f;
  auto* origin = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] bank [2][2][2];\n"
      "  logic [7:0] mirror [2][2][2];\n"
      "  initial begin\n"
      "    bank[0][0][0] = 8'b0x11z000;\n"
      "    bank[0][0][1] = 8'h3C;\n"
      "    mirror[0][0] = bank[0][0];\n"
      "    mirror[0][0][0] = 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f, "bank[0][0][0]");
  ASSERT_NE(origin, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* overwritten = f.ctx.FindVariable("mirror[0][0][0]");
  auto* carried = f.ctx.FindVariable("mirror[0][0][1]");
  ASSERT_NE(overwritten, nullptr);
  ASSERT_NE(carried, nullptr);
  EXPECT_EQ(origin->value.words[0].aval & 0xFFu, 0x70u);
  EXPECT_EQ(origin->value.words[0].bval & 0xFFu, 0x48u);
  EXPECT_EQ(overwritten->value.words[0].aval & 0xFFu, 0xFFu);
  EXPECT_EQ(carried->value.words[0].aval & 0xFFu, 0x3Cu);
}

TEST(MultidimensionalArraySimulation, BlockLocalArrayBuildsEveryDimension) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[0:1][0:2];\n"
      "    a[1][2] = 7;\n"
      "    result = a[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(MultidimensionalArraySimulation, BlockLocalArrayBuildsEverySizeFormDim) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[2][3];\n"
      "    a[1][2] = 7;\n"
      "    result = a[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(MultidimensionalArraySimulation,
     BlockLocalArrayRecordsEveryDimensionSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int a[0:1][0:2];\n"
      "    result = 0;\n"
      "    foreach (a[i, j]) result = result + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

TEST(MultidimensionalArraySimulation, ModuleScopeArrayAgreesWithTheBlockLocal) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[0:1][0:2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[1][2] = 7;\n"
      "    result = a[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(MultidimensionalArraySimulation,
     WriteToAnAbsentCompoundElementIsNoOperation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a [0:1][0:2];\n"
      "  int i;\n"
      "  initial begin\n"
      "    i = 5;\n"
      "    a[i][0] = 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a[5][0]"), nullptr);
}

TEST(MultidimensionalArraySimulation, RepeatedAbsentCompoundWriteMakesNoCells) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a [0:1][0:2];\n"
      "  int i;\n"
      "  initial begin\n"
      "    for (i = 5; i < 7; i = i + 1)\n"
      "      a[i][0] = 7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a[5][0]"), nullptr);
  EXPECT_EQ(f.ctx.FindVariable("a[6][0]"), nullptr);
}

TEST(MultidimensionalArraySimulation, WriteToAPresentCompoundElementReachesIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte a [0:1][0:2];\n"
      "  int i;\n"
      "  initial begin\n"
      "    i = 1;\n"
      "    a[i][2] = 8'd7;\n"
      "  end\n"
      "endmodule\n",
      f, "a[1][2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(MultidimensionalArraySimulation,
     UseSitePackedDimStacksOnTheTypedefsWidth) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  int result;\n"
      "  initial begin\n"
      "    nib [1:0] x;\n"
      "    x = 8'hA5;\n"
      "    result = x;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xA5u);
}

TEST(MultidimensionalArraySimulation, UseSitePackedDimStacksInASubroutineBody) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  int result;\n"
      "  function automatic int widen(input int seed);\n"
      "    nib [1:0] x;\n"
      "    x = seed;\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial result = widen(8'hA5);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xA5u);
}

TEST(MultidimensionalArraySimulation,
     UseSitePackedDimOnAScalarTypedefIsItself) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef bit flag;\n"
      "  int result;\n"
      "  initial begin\n"
      "    flag [3:0] f;\n"
      "    f = 4'hD;\n"
      "    result = f;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xDu);
}

TEST(MultidimensionalArraySimulation, QueueTypedefLocalInAFunctionIsAQueue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef int q_t[$];\n"
      "  int result;\n"
      "  function automatic int fill();\n"
      "    q_t qu;\n"
      "    qu.push_back(7);\n"
      "    qu.push_back(8);\n"
      "    qu.push_back(9);\n"
      "    return qu.size() * 100 + qu[1];\n"
      "  endfunction\n"
      "  initial result = fill();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 308u);
}

TEST(MultidimensionalArraySimulation, ArrayTypedefLocalInAFunctionHasElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef int arr_t[4];\n"
      "  int result;\n"
      "  function automatic int fill();\n"
      "    arr_t a;\n"
      "    a[0] = 5;\n"
      "    a[3] = 9;\n"
      "    return a[0] * 100 + a[3];\n"
      "  endfunction\n"
      "  initial result = fill();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 509u);
}

TEST(MultidimensionalArraySimulation, AggregateTypedefLocalsInAnInitialBlock) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef int q_t[$];\n"
      "  typedef int arr_t[4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q_t qu;\n"
      "    arr_t a;\n"
      "    qu.push_back(4);\n"
      "    qu.push_back(6);\n"
      "    a[2] = 7;\n"
      "    result = qu.size() * 100 + qu[1] * 10 + a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 267u);
}

TEST(MultidimensionalArraySimulation,
     BitOfPackedSubfieldOfUnpackedElementWrites) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  initial begin\n"
      "    y[0] = 0;\n"
      "    y[0][3][1] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      "y[0]");
  EXPECT_EQ(v, 0x02000000u);
}

TEST(MultidimensionalArraySimulation,
     BitOfPackedSubfieldOfPackedVariableWrites) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    x[1][3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(v, 0x0800u);
}

TEST(MultidimensionalArraySimulation,
     SubfieldOfUnpackedElementStillWritesWhole) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  initial begin\n"
      "    y[1] = 32'h00000001;\n"
      "    y[1][2] = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      "y[1]");
  EXPECT_EQ(v, 0x00AB0001u);
}

TEST(MultidimensionalArraySimulation, PartSelectOfPackedSubfieldWrites) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  initial begin\n"
      "    y[0] = 0;\n"
      "    y[0][3][7:4] = 4'hC;\n"
      "  end\n"
      "endmodule\n",
      "y[0]");
  EXPECT_EQ(v, 0xC0000000u);
}

TEST(MultidimensionalArraySimulation, OutOfRangeSubfieldIndexWritesNothing) {
  auto src =
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  logic [1:0][7:0] x;\n"
      "  initial begin\n"
      "    y[0] = 0;\n"
      "    x = 0;\n"
      "    y[0][2][9] = 1'b1;\n"
      "    x[0][8] = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "y[0]"), 0u);
  EXPECT_EQ(RunAndGet(src, "x"), 0u);
}

TEST(MultidimensionalArraySimulation, NonblockingBitOfPackedSubfieldWrites) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  initial begin\n"
      "    y[0] = 0;\n"
      "    y[0][3][1] <= 1'b1;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      "y[0]");
  EXPECT_EQ(v, 0x02000000u);
}

TEST(MultidimensionalArraySimulation, SubfieldAndBitOfUnpackedElementRead) {
  auto src =
      "module t;\n"
      "  logic [3:0][7:0] y[1:0];\n"
      "  logic [7:0] sub;\n"
      "  logic b;\n"
      "  initial begin\n"
      "    y[0] = 32'h5A000000;\n"
      "    sub = y[0][3];\n"
      "    b = y[0][3][1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "sub"), 0x5Au);
  EXPECT_EQ(RunAndGet(src, "b"), 1u);
}

TEST(MultidimensionalArraySimulation, ConcatLvalueBitOfPackedSubfieldIsOneBit) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [1:0][7:0] x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    {x[0], x[1][3]} = 9'h157;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(v, 0x08ABu);
}

TEST(MultidimensionalArraySimulation, ThirdPackedDimensionBitWrites) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [1:0][1:0][7:0] z;\n"
      "  initial begin\n"
      "    z = 0;\n"
      "    z[1][0][3] = 1'b1;\n"
      "    z[0][1][7] = 1'b1;\n"
      "    z[1][1] = 8'h5A;\n"
      "  end\n"
      "endmodule\n",
      "z");
  EXPECT_EQ(v, 0x5A088000u);
}

TEST(MultidimensionalArraySimulation, ThirdPackedDimensionSubfieldAndBitRead) {
  auto src =
      "module t;\n"
      "  logic [1:0][1:0][7:0] z;\n"
      "  logic [7:0] sub;\n"
      "  logic b;\n"
      "  initial begin\n"
      "    z = 32'h89ABCDEF;\n"
      "    sub = z[1][0];\n"
      "    b = z[0][1][6];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "sub"), 0xABu);
  EXPECT_EQ(RunAndGet(src, "b"), 1u);
}

TEST(MultidimensionalArraySimulation, ThirdPackedDimensionPartSelectWrites) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [1:0][1:0][7:0] z;\n"
      "  initial begin\n"
      "    z = 0;\n"
      "    z[0][1][7:4] = 4'hC;\n"
      "  end\n"
      "endmodule\n",
      "z");
  EXPECT_EQ(v, 0x0000C000u);
}

TEST(MultidimensionalArraySimulation, InnerPackedDimensionRangeAsDeclared) {
  auto src =
      "module t;\n"
      "  logic [1:0][0:7] w;\n"
      "  logic b;\n"
      "  initial begin\n"
      "    w = 16'h8000;\n"
      "    b = w[1][0];\n"
      "    w = 0;\n"
      "    w[1][0] = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "b"), 1u);
  EXPECT_EQ(RunAndGet(src, "w"), 0x8000u);
}

TEST(MultidimensionalArraySimulation, PropertyTakesAModuleTypedefsFixedDim) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef int arr_t[3];\n"
      "  class C; arr_t a; endclass\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.a[1] = 9;\n"
      "    c.a[2] = 4;\n"
      "    result = c.a[1] * 10 + c.a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 94u);
}

TEST(MultidimensionalArraySimulation, PropertyTakesAUnitTypedefsQueueDim) {
  auto v = RunAndGet(
      "typedef int q_t[$];\n"
      "class C; q_t q; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.q.push_back(7);\n"
      "    c.q.push_back(8);\n"
      "    c.q.push_back(9);\n"
      "    result = c.q.size() * 100 + c.q[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 308u);
}

TEST(MultidimensionalArraySimulation, PropertyTakesAUnitTypedefsAssocDim) {
  auto v = RunAndGet(
      "typedef int a_t[string];\n"
      "class C; a_t m; endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    c.m[\"x\"] = 3;\n"
      "    c.m[\"y\"] = 4;\n"
      "    result = c.m.num() * 10 + c.m[\"y\"];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 24u);
}

TEST(MultidimensionalArraySimulation, PropertyTakesAPackageTypedefsQueueDim) {
  auto v = RunAndGet(
      "package p;\n"
      "  typedef int q_t[$];\n"
      "  class C; q_t q; endclass\n"
      "endpackage\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static p::C c = new;\n"
      "    c.q.push_back(5);\n"
      "    c.q.push_back(6);\n"
      "    result = c.q.size() * 10 + c.q[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 25u);
}

TEST(MultidimensionalArraySimulation, PackedArrayOfPackedArraysIndexedPerDim) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [3:0][7:0] joe [1:10];\n"
      "  typedef bit [1:5] bsix;\n"
      "  bsix [1:10] v5;\n"
      "  initial begin\n"
      "    joe[6] = 32'h00001234;\n"
      "    joe[7] = 0;\n"
      "    joe[7][3:2] = joe[6][1:0];\n"
      "    joe[7][0] = joe[6][1] + 1;\n"
      "    $display(\"%h %0d %0d\", joe[7], joe[7][3:2], joe[7][2]);\n"
      "    v5 = 0; v5[1] = 5'b10101; v5[1][5] = 1'b0; v5[2][2] = 1'b1;\n"
      "    $display(\"%0d %0d %0d\", v5[1], v5[2], v5[10]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "12340013 4660 52\n20 8 0\n");
}

TEST(MultidimensionalArraySimulation, QueriesNumberEachPackedDimension) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [3:0][7:0] joe [1:10];\n"
      "  initial begin\n"
      "    $display(\"%0d %0d\", $dimensions(joe), "
      "$unpacked_dimensions(joe));\n"
      "    $display(\"%0d %0d %0d %0d\", $size(joe, 2), $left(joe, 2),\n"
      "             $right(joe, 2), $increment(joe, 2));\n"
      "    $display(\"%0d %0d %0d\", $size(joe, 3), $left(joe, 3), $right(joe, "
      "3));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1\n4 3 0 1\n8 7 0\n");
}

TEST(MultidimensionalArraySimulation, TypedefDefinesThePackedDimensions) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef logic [1:0][3:0] T;\n"
      "  initial begin\n"
      "    T x;\n"
      "    x = 8'hA5;\n"
      "    $display(\"%h %h %b %b\", x[1], x[0], x[1][2], x[0][2]);\n"
      "    x[0] = 4'h3;\n"
      "    $display(\"%h\", x);\n"
      "    x = '{1, 2};\n"
      "    $display(\"%h\", x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a 5 0 1\na3\n12\n");
}

TEST(MultidimensionalArraySimulation, TypedefDefinesAModuleVariablesDims) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef logic [1:0][3:0] T;\n"
      "  T x;\n"
      "  initial begin\n"
      "    x = 8'hA5;\n"
      "    $display(\"%h %h %b %b\", x[1], x[0], x[1][2], x[0][2]);\n"
      "    x[0] = 4'h3;\n"
      "    $display(\"%h\", x);\n"
      "    x = '{1, 2};\n"
      "    $display(\"%h\", x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a 5 0 1\na3\n12\n");
}

TEST(MultidimensionalArraySimulation, IndexPastANamedVectorElementSelectsBits) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef int myint;\n"
      "  typedef struct packed { logic [3:0] a, b; } p_t;\n"
      "  byte_t mem [4];\n"
      "  myint m [4];\n"
      "  p_t pm [2];\n"
      "  initial begin\n"
      "    mem[0] = 8'h00;\n"
      "    mem[1] = 8'h00;\n"
      "    m[0] = 0;\n"
      "    pm[1] = 8'h00;\n"
      "    mem[0][3] = 1'b1;\n"
      "    mem[0][7:6] = 2'b11;\n"
      "    mem[1][0] <= 1'b1;\n"
      "    m[0][3] = 1'b1;\n"
      "    pm[1][0] = 1'b1;\n"
      "    #1 $display(\"%h %h %b %0d %h\", mem[0], mem[1], mem[0][3], m[0],\n"
      "                pm[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "c8 01 1 8 01\n");
}

}  // namespace
