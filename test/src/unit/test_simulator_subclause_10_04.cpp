#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ProceduralAssignSim, AssignInCalledTask) {
  auto result = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  task do_set();\n"
      "    x = 55;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    do_set();\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 55u);
}

TEST(ProceduralAssignSim, AssignInCalledFunction) {
  auto result = RunAndGet(
      "module t;\n"
      "  function int double_it(int v);\n"
      "    int tmp;\n"
      "    tmp = v * 2;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = double_it(21);\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(result, 42u);
}

TEST(ProceduralAssignSim, BlockingFlowIsSequentialOverwrite) {
  auto a = RunAndGet(
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    a = b;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(a, 2u);
  auto b = RunAndGet(
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    a = b;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(b, 2u);
}

TEST(ProceduralAssignSim, AggregateVariableWholeArrayLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [7:0] m0, m1, m2, m3;\n"
      "  initial begin\n"
      "    mem = '{8'hAA, 8'hBB, 8'hCC, 8'hDD};\n"
      "    m0 = mem[0]; m1 = mem[1]; m2 = mem[2]; m3 = mem[3];\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design, {{"m0", 0xAAu}, {"m1", 0xBBu}, {"m2", 0xCCu}, {"m3", 0xDDu}});
}

TEST(ProceduralAssignSim, PackedPartSelectLhs) {
  auto pk = RunAndGet(
      "module t;\n"
      "  logic [7:0] pk;\n"
      "  initial begin\n"
      "    pk = 8'h00;\n"
      "    pk[6:3] = 4'hF;\n"
      "  end\n"
      "endmodule\n",
      "pk");
  EXPECT_EQ(pk, 0x78u);
}

TEST(ProceduralAssignSim, UnpackedArraySliceLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a [0:3];\n"
      "  logic [7:0] a0, a3, asum;\n"
      "  initial begin\n"
      "    a = '{4'h0, 4'h0, 4'h0, 4'h0};\n"
      "    a[1:2] = '{4'h3, 4'h4};\n"
      "    a0 = a[0]; a3 = a[3]; asum = a[1] + a[2];\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a0", 0u}, {"a3", 0u}, {"asum", 7u}});
}

TEST(ProceduralAssignSim, PackedStructWholeAssignLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [3:0] hi; logic [3:0] lo; } ps;\n"
      "  logic [3:0] hi, lo;\n"
      "  initial begin\n"
      "    ps = 8'hC5;\n"
      "    hi = ps.hi; lo = ps.lo;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"hi", 0xCu}, {"lo", 0x5u}});
}

TEST(ProceduralAssignSim, PackedUnionWholeAssignLhs) {
  auto b = RunAndGet(
      "module t;\n"
      "  union packed { logic [7:0] byte_v; logic [1:0][3:0] pair; } pu;\n"
      "  logic [7:0] out;\n"
      "  initial begin\n"
      "    pu = 8'hA3;\n"
      "    out = pu.byte_v;\n"
      "  end\n"
      "endmodule\n",
      "out");
  EXPECT_EQ(b, 0xA3u);
}

TEST(ProceduralAssignSim, PackedBitSelectLhs) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] bsv;\n"
      "  initial begin\n"
      "    bsv = 8'h00;\n"
      "    bsv[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      "bsv");
  EXPECT_EQ(v, 0x08u);
}

TEST(ProceduralAssignSim, NonblockingFlowSwapsInSameBlock) {
  auto a = RunAndGet(
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(a, 2u);
  auto b = RunAndGet(
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(b, 1u);
}

TEST(ClassMethodAssignSim, AnArrayPatternAssignsFromAClassMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int fill();\n"
                      "    logic [7:0] mem [0:2];\n"
                      "    mem = '{8'h11, 8'h22, 8'h33};\n"
                      "    return mem[0] + mem[1] + mem[2];\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.fill();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x66u);
}

TEST(ClassMethodAssignSim, AStreamingTargetAssignsFromAClassMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int split();\n"
                      "    logic [7:0] hi, lo;\n"
                      "    {>>8{hi, lo}} = 16'hDEAD;\n"
                      "    return {hi, lo};\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.split();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0xDEADu);
}

TEST(ClassMethodAssignSim, AConcatenationTargetAssignsFromAClassMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int split();\n"
                      "    logic [3:0] a, b;\n"
                      "    {a, b} = 8'h5C;\n"
                      "    return a * 256 + b;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.split();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x50Cu);
}

TEST(ClassMethodAssignSim, AnUnpackedSliceAssignsFromAClassMethod) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  function int slice();\n"
                      "    logic [3:0] a [0:3];\n"
                      "    a = '{4'h0, 4'h0, 4'h0, 4'h0};\n"
                      "    a[1:2] = '{4'h3, 4'h4};\n"
                      "    return (a[1] + a[2]) * 16 + a[0] + a[3];\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = new;\n"
                      "    result = c.slice();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x70u);
}

}  // namespace
