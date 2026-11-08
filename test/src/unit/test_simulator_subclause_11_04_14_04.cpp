#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StreamingDynamicDataSim, PackWithSlicesSelectedElements) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBu);
}

TEST(StreamingDynamicDataSim, PackWithFixedRangeSelectsSubset) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBBCCu);
}

TEST(StreamingDynamicDataSim, PackWithSimpleIndexSelectsSingleElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "result");
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "streaming unpack with-range exceeds fixed array bounds", 4,
                    "11.4.14.4"));
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
  auto* vlen = RunAndFindVar(
      "module t;\n"
      "  int len;\n"
      "  logic [7:0] payload[8];\n"
      "  initial begin\n"
      "    {>> {len, payload with [0 +: len]}} = {32'd3, 24'hAABBCC};\n"
      "  end\n"
      "endmodule\n",
      f, "len");
  ASSERT_NE(vlen, nullptr);
  EXPECT_EQ(vlen->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("payload[0]")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("payload[1]")->value.ToUint64(), 0xBBu);
  EXPECT_EQ(f.ctx.FindVariable("payload[2]")->value.ToUint64(), 0xCCu);
}

TEST(StreamingDynamicDataSim, PackWithMinusPartSelectSelectsTrailingElements) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    arr[2] = 8'hCC;\n"
      "    arr[3] = 8'hDD;\n"
      "    result = {>> byte {arr with [3 -: 2]}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCCDDu);
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
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABB0000u);
}

TEST(StreamingDynamicDataSim, WithRangeUsesPreviousValueOfLaterUnpackedField) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] payload[8];\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = 2;\n"
      "    {>> {payload with [0 +: n], n}} = 48'hAABB00000005;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("payload[0]")->value.ToUint64(), 0xAAu);
  EXPECT_EQ(f.ctx.FindVariable("payload[1]")->value.ToUint64(), 0xBBu);
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 5u);
}

TEST(StreamingDynamicDataSim, PackQueueWithRangeSelectsSubset) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte q[$];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    q.push_back(8'hAA);\n"
      "    q.push_back(8'hBB);\n"
      "    q.push_back(8'hCC);\n"
      "    result = {>> byte {q with [0 +: 2]}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBu);
}

TEST(StreamingDynamicDataSim, PackQueueWithRangeBeyondSizeUsesDefault) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte q[$];\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    q.push_back(8'hAA);\n"
      "    q.push_back(8'hBB);\n"
      "    result = {>> byte {q with [0 +: 4]}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABB0000u);
}

TEST(StreamingDynamicDataSim, UnpackQueuePartialRangeKeepsRemainder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  initial begin\n"
      "    q.push_back(8'h11);\n"
      "    q.push_back(8'h22);\n"
      "    q.push_back(8'h33);\n"
      "    q.push_back(8'h44);\n"
      "    {>> byte {q with [1 +: 2]}} = 16'hEEFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x11u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0xEEu);
  EXPECT_EQ(q->elements[2].ToUint64(), 0xFFu);
  EXPECT_EQ(q->elements[3].ToUint64(), 0x44u);
}

TEST(StreamingDynamicDataSim, PackFourStateOversizeRangePadsWithX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr[2];\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    result = {>> byte {arr with [0 +: 4]}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0xAABBFFFFu);
  EXPECT_EQ(var->value.words[0].bval, 0x0000FFFFu);
}

TEST(StreamingDynamicDataSim, PackTwoStateOversizeRangePadsWithZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] arr[2];\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAA;\n"
      "    arr[1] = 8'hBB;\n"
      "    result = {>> byte {arr with [0 +: 4]}};\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0xAABB0000u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(StreamingDynamicDataSim, PackDynamicArrayWithRangeSelectsSubset) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] d [] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  logic [15:0] result;\n"
      "  initial result = {>> byte {d with [0 +: 2]}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAABBu);
}

TEST(StreamingDynamicDataSim, OutOfRangeWithRangeNames11_4_14_4) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] cells[4];\n"
      "  initial {>> byte {cells with [0 +: 6]}} = 48'h112233445566;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "with-range exceeds fixed array bounds", 3,
                            "11.4.14.4"));
}

TEST(StreamingDynamicDataSim, OutOfRangeForwardWithRangeNames11_4_14_4) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int want;\n"
      "  logic [7:0] cells[4];\n"
      "  initial {>> {want, cells with [0 +: want]}} = {32'd9, 32'hAABBCCDD};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "with-range exceeds fixed array bounds", 4,
                            "11.4.14.4"));
}

TEST(StreamingDynamicDataSim,
     OutOfBoundsSelectElementIsChargedToTheGreedyQueueBudget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  byte q[$];\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    q.push_back(8'hE7);\n"
      "    q.push_back(8'hE8);\n"
      "    q.push_back(8'hE9);\n"
      "    {>> {a[9], q}} = 24'hC3A55A;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x87u);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x4Au);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x1Au);
}

TEST(StreamingDynamicDataSim,
     ForwardResolveOutOfBoundsSelectElementStillClaimsItsBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] n;\n"
      "  logic [7:0] payload[4];\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    n = 8'hE0;\n"
      "    payload[0] = 8'h71;\n"
      "    payload[1] = 8'h72;\n"
      "    payload[2] = 8'h73;\n"
      "    payload[3] = 8'h74;\n"
      "    {>> {n, a[9], payload with [0 +: n]}} = 25'h05C35A;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 0x02u);
  EXPECT_EQ(f.ctx.FindVariable("payload[0]")->value.ToUint64(), 0xC3u);
  EXPECT_EQ(f.ctx.FindVariable("payload[1]")->value.ToUint64(), 0x5Au);
  EXPECT_EQ(f.ctx.FindVariable("payload[2]")->value.ToUint64(), 0x73u);
  EXPECT_EQ(f.ctx.FindVariable("payload[3]")->value.ToUint64(), 0x74u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x1Au);
}

TEST(StreamingDynamicDataSim, UnpackFromAQueueSourceFillsADynamicArray) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i_header, i_len, i_crc;\n"
      "  byte i_data[];\n"
      "  int o_header, o_len, o_crc;\n"
      "  byte o_data[];\n"
      "  int n, last;\n"
      "  initial begin\n"
      "    byte pkt[$];\n"
      "    i_header = 12;\n"
      "    i_len = 5;\n"
      "    i_crc = 42;\n"
      "    i_data = new[5];\n"
      "    i_data[0] = 1; i_data[1] = 2; i_data[2] = 3;\n"
      "    i_data[3] = 4; i_data[4] = 5;\n"
      "    pkt = {<< 8 {i_header, i_len, i_crc, i_data}};\n"
      "    {<< 8 {o_header, o_len, o_crc, o_data}} = pkt;\n"
      "    n = o_data.size();\n"
      "    last = o_data[4];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.FindVariable("o_header")->value.ToUint64(), 12u);
  EXPECT_EQ(f.ctx.FindVariable("o_len")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("o_crc")->value.ToUint64(), 42u);
  EXPECT_EQ(f.ctx.FindVariable("n")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 5u);
}

TEST(StreamingWithSim, PacketExampleThroughClassProperties) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Packet;\n"
      "    int header; int len; byte payload[]; int crc;\n"
      "  endclass\n"
      "  byte stream[$];\n"
      "  initial begin\n"
      "    Packet p, q;\n"
      "    p = new; p.header = 32'h11223344; p.len = 3; p.crc = 6;\n"
      "    p.payload = new[3];\n"
      "    p.payload[0] = 1; p.payload[1] = 2; p.payload[2] = 3;\n"
      "    stream = {<< byte{p.header, p.len, p.payload, p.crc}};\n"
      "    q = new;\n"
      "    {<< byte{q.header, q.len, q.payload with [0 +: q.len], q.crc}} =\n"
      "        stream;\n"
      "    $display(\"%0d %h %0d %0d %0d %0d %0d %0d\", stream.size(),\n"
      "             q.header, q.len, q.payload[0], q.payload[1],\n"
      "             q.payload[2], q.crc, q.payload.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "15 11223344 3 1 2 3 6 3\n");
}

TEST(StreamingWithSim, ReverseUnpackRangeReadsAnEarlierTarget) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int header, len, crc; byte payload[];\n"
      "  byte stream[$];\n"
      "  initial begin\n"
      "    stream = {8'h06, 8'h00, 8'h00, 8'h00, 8'h03, 8'h02, 8'h01, 8'h03,\n"
      "              8'h00, 8'h00, 8'h00, 8'h44, 8'h33, 8'h22, 8'h11};\n"
      "    {<< byte{header, len, payload with [0 +: len], crc}} = stream;\n"
      "    $display(\"%h %0d %0d %0d %0d %0d %0d\", header, len, payload[0],\n"
      "             payload[1], payload[2], crc, payload.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "11223344 3 1 2 3 6 3\n");
}

TEST(StreamWithRangeSim, MissingItemsAreXAndDescendingRangesRunLeftToRight) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [7:0] q[$];\n"
                       "  logic [7:0] a [3:0], d [3:0];\n"
                       "  logic [31:0] r;\n"
                       "  logic [15:0] s;\n"
                       "  initial begin\n"
                       "    q = '{8'hAA, 8'hBB};\n"
                       "    r = {>> {q with [0 +: 4]}};\n"
                       "    a[3] = 8'h33; a[2] = 8'h22;\n"
                       "    s = {>> {a with [3:2]}};\n"
                       "    {>> {d with [3:2]}} = 16'h4455;\n"
                       "    $display(\"%h %h %h %h\", r, s, d[3], d[2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "aabbxxxx 3322 44 55\n");
}

}  // namespace
