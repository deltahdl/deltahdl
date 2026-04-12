#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AssignmentOverviewSim, ProceduralAssignMemoryWord) {
  auto result = RunAndGet(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  logic [7:0] out;\n"
      "  initial begin\n"
      "    mem[2] = 8'hAB;\n"
      "    out = mem[2];\n"
      "  end\n"
      "endmodule\n",
      "out");
  EXPECT_EQ(result, 0xABu);
}

TEST(AssignmentOverviewSim, ProceduralAssignArrayElement) {
  auto result = RunAndGet(
      "module t;\n"
      "  int arr [4];\n"
      "  int out;\n"
      "  initial begin\n"
      "    arr[1] = 99;\n"
      "    out = arr[1];\n"
      "  end\n"
      "endmodule\n",
      "out");
  EXPECT_EQ(result, 99u);
}

TEST(AssignmentOverviewSim, ProceduralAssignBitSelect) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'h00;\n"
      "    v[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(result, 0x08u);
}

TEST(AssignmentOverviewSim, ProceduralAssignPartSelect) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'h00;\n"
      "    v[3:0] = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(result, 0x0Au);
}

TEST(AssignmentOverviewSim, ProceduralAssignConcatenationLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    {a, b} = 8'hA5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xAu);
  EXPECT_EQ(vb->value.ToUint64(), 0x5u);
}

TEST(AssignmentOverviewSim, ProceduralAssignWholeArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a [2];\n"
      "  int b [2];\n"
      "  int out;\n"
      "  initial begin\n"
      "    a[0] = 10;\n"
      "    a[1] = 20;\n"
      "    b = a;\n"
      "    out = b[0] + b[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(AssignmentOverviewSim, ProceduralAssignIndexedPartSelect) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'h00;\n"
      "    v[4+:4] = 4'hF;\n"
      "  end\n"
      "endmodule\n",
      "v");
  EXPECT_EQ(result, 0xF0u);
}

}  // namespace
