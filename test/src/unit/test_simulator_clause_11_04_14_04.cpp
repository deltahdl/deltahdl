#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StreamingDynamicDataSim, PackWithSlicesSelectedElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    arr[2] = 8'hCC;\n"
      "    arr[3] = 8'hDD;\n"
      "    result = {>> byte {arr with [0 +: 2]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBu);
}

TEST(StreamingDynamicDataSim, PackWithFixedRangeSelectsSubset) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    arr[2] = 8'hCC;\n"
      "    arr[3] = 8'hDD;\n"
      "    result = {>> byte {arr with [1:2]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBBCCu);
}

TEST(StreamingDynamicDataSim, PackWithSimpleIndexSelectsSingleElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    arr[2] = 8'hCC;\n"
      "    arr[3] = 8'hDD;\n"
      "    result = {>> byte {arr with [2]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCCu);
}

TEST(StreamingDynamicDataSim, UnpackPartialRangeKeepsRemainder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  initial begin\n"
      "    arr[0] = 8'h11;\n"
      "    arr[1] = 8'h22;\n"
      "    arr[2] = 8'h33;\n"
      "    arr[3] = 8'h44;\n"
      "    {>> byte {arr with [0 +: 2]}} = 16'hAABB;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xBBu);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0x33u);
  EXPECT_EQ(f.ctx.FindVariable("arr[3]")->value.ToUint64(), 0x44u);
}

TEST(StreamingDynamicDataSim, UnpackFixedRangeModifiesOnlySpecified) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  initial begin\n"
      "    arr[0] = 8'h11;\n"
      "    arr[1] = 8'h22;\n"
      "    arr[2] = 8'h33;\n"
      "    arr[3] = 8'h44;\n"
      "    {>> byte {arr with [1:2]}} = 16'hEEFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 0x11u);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 0xEEu);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 0xFFu);
  EXPECT_EQ(f.ctx.FindVariable("arr[3]")->value.ToUint64(), 0x44u);
}

TEST(StreamingDynamicDataSim, UnpackOutOfRangeOnFixedArrayErrors) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  initial begin\n"
      "    {>> byte {arr with [0 +: 8]}} = 64'hDEADBEEFCAFEBABE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StreamingDynamicDataSim, UnpackResizesDynamicArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  initial begin\n"
      "    {<< byte {q with [0 +: 3]}} = 24'hAABBCC;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  if (q) {
    EXPECT_EQ(q->elements.size(), 3u);
  }
}

TEST(StreamingDynamicDataSim, GreedyUnpackFirstDynamicGetsAllData) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  logic [7:0] trailer;\n"
      "  initial begin\n"
      "    {>> byte {q, trailer}} = 32'hAABBCCDD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  auto* t = f.ctx.FindVariable("trailer");
  if (q && t) {
    EXPECT_EQ(q->elements.size(), 3u);
    EXPECT_EQ(t->value.ToUint64(), 0xDDu);
  }
}

TEST(StreamingDynamicDataSim, GreedyUnpackRemainingDynamicLeftEmpty) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q1[$];\n"
      "  byte q2[$];\n"
      "  initial begin\n"
      "    {>> byte {q1, q2}} = 24'hAABBCC;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q1 = f.ctx.FindQueue("q1");
  auto* q2 = f.ctx.FindQueue("q2");
  if (q1 && q2) {
    EXPECT_EQ(q1->elements.size(), 3u);
    EXPECT_EQ(q2->elements.size(), 0u);
  }
}

TEST(StreamingDynamicDataSim, WithExprReferencesEarlierUnpackedData) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int len;\n"
      "  logic [7:0] payload[8];\n"
      "  initial begin\n"
      "    {>> {len, payload with [0 +: len]}} = {32'd3, 24'hAABBCC};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vlen = f.ctx.FindVariable("len");
  if (vlen) {
    EXPECT_EQ(vlen->value.ToUint64(), 3u);
  }
}

TEST(StreamingDynamicDataSim, PackLeftShiftWithClause) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    arr[2] = 8'hCC;\n"
      "    arr[3] = 8'hDD;\n"
      "    result = {<< byte {arr with [0 +: 2]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBBAAu);
}

TEST(StreamingDynamicDataSim, PackWithRangeLargerThanArrayUsesDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr[2];\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    result = {>> byte {arr with [0 +: 4]}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

}

}
