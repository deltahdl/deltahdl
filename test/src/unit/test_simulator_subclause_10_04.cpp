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

// §10.4 lists "aggregate variables (Clause 7)" as a legal procedural-assignment
// left-hand form. Assigning a whole unpacked array with an array literal drives
// each element and observes that the aggregate LHS received the value.
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

// §10.4 lists "part-selects ... of packed arrays" as a legal LHS form. A
// procedural assignment to a packed part-select updates exactly the selected
// bit range and leaves the surrounding bits untouched.
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

// §10.4 lists "slices of unpacked arrays" as a legal LHS form. A procedural
// assignment to an unpacked slice writes exactly the sliced elements and leaves
// the neighbours untouched. The check is order-agnostic (element ordering
// within the slice is governed by Clause 7, not §10.4): it observes that both
// sliced nibbles landed inside the slice and only there.
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

// §10.4 form "aggregate variables (Clause 7)", built from §7.2 real syntax: a
// whole packed-struct variable is a legal procedural-assignment LHS. Assigning
// a value to the struct as a whole drives its members, observed via the
// members.
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

// §10.4 form "aggregate variables (Clause 7)", built from §7.3 real syntax: a
// whole packed-union variable is a legal procedural-assignment LHS. Assigning
// to the union writes the shared storage, observed through a member read.
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

// §10.4 form "bit-selects ... of packed arrays": a procedural assignment to a
// single bit-select updates only that bit, observed at runtime.
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

}  // namespace
