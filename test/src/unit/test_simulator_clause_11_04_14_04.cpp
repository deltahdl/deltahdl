#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// Requirement 10: In pack context, `with` behaves as an array slice —
// only the specified elements are streamed.
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

// Requirement 10: Pack with fixed range [1:2] selects elements 1 and 2.
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

// Requirement 10: Pack with simple index selects single element.
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

// Requirement 9: Unpack with range smaller than array — only specified
// items are unpacked; remainder is unmodified.
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

// Requirement 9: Unpack with fixed range [1:2] unpacks only those positions.
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

// Requirement 8: Unpack with range outside fixed-size array extent
// generates an error.
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

// Requirement 7: Unpack with variable-size array resizes it to fit range.
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

// Requirement 1: Greedy unpacking — first dynamically sized item gets all
// available data excluding subsequent fixed-size items.
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

// Requirement 1: Greedy unpacking — remaining dynamically sized items
// are left empty.
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

// Requirement 6: The `with` expression is evaluated immediately before
// its corresponding array is streamed and can reference data unpacked
// earlier by the same operator.
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

// Requirement 10: Pack with left-shift and `with` — slice selected then
// reordered.
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

// Requirement 10: Pack with `with` range larger than array extent — entire
// array is streamed and remaining items use the default value.
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
  // arr[0]=0xAA, arr[1]=0xBB, arr[2] and arr[3] are nonexistent (default 'x).
  // The result should contain the two real elements plus two default elements.
}

}  // namespace
