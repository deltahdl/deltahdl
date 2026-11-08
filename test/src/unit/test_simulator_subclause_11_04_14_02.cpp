#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StreamReordering, StreamingRightShiftIntegration) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {>> {8'hAB}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(StreamReordering, StreamingLeftShiftIntegration) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {<< {8'hAB}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xD5u);
}

TEST(StreamReordering, TypeSliceSizeByteReversesBytesRealSource) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] result;\n"
      "  initial result = {<< byte {16'hABCD}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDABu);
}

TEST(StreamReordering, TypeSliceSizeShortintUsesTypeBitWidthRealSource) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = {<< shortint {32'hABCD1234}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234ABCDu);
}

TEST(StreamReordering, ParameterSliceSizeResolvesToBlockWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter WIDTH = 8;\n"
      "  logic [15:0] result;\n"
      "  initial result = {<< (WIDTH+0) {16'hABCD}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDABu);
}

TEST(StreamReordering, RightShiftIgnoresSliceSizeNonDivisible) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [5:0] result;\n"
      "  initial result = {>> 4 {6'b110101}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b110101u);
}

TEST(StreamReordering, LeftShiftShortLastBlock) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [5:0] result;\n"
      "  initial result = {<< 4 {6'b110101}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b010111u);
}

TEST(StreamReordering, LeftShift16BitSliceSwap) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = {<< 16 {32'hABCD1234}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234ABCDu);
}

TEST(StreamReordering, LeftShiftSliceSizeEqualsWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = {<< 8 {8'hAB}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(StreamReordering, NestedStreamingReordering) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] result;\n"
      "  initial result = {<< 2 { {<< {4'b1101}} }};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0b1110u);
}

TEST(StreamReordering, PackZeroSliceSizeNames11_4_14_2) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter SZ = 8;\n"
      "  logic [15:0] result;\n"
      "  initial result = {<< (SZ-8) {16'hABCD}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice_size for streaming operator", 4,
                            "11.4.14.2"));
}

TEST(StreamReordering, UnpackZeroSliceSizeNames11_4_14_2) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter SZ = 4;\n"
      "  logic [7:0] p, q;\n"
      "  initial {<< (SZ-4) {p, q}} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "slice_size for streaming operator", 4,
                            "11.4.14.2"));
}

TEST(StreamReordering, LeftShiftWideBlocksSwapWhole) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [191:0] result;\n"
      "  initial result = {<< 96 {192'h0123_4567_89AB_CDEF_0F1E_2D3C_"
      "FEDC_BA98_7654_3210_0F0F_A5A5}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 3u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0x89ABCDEF0F1E2D3Cu);
  EXPECT_EQ(var->value.words[1].aval, 0x0F0FA5A501234567u);
  EXPECT_EQ(var->value.words[2].aval, 0xFEDCBA9876543210u);
}

TEST(StreamReordering, LeftShiftWideShortLastBlockKeepsItsSize) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [159:0] result;\n"
      "  initial result = {<< 96 {160'hABCD_EF01_2345_6789_"
      "FEDC_BA98_7654_3210_0F0F_A5A5}};\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 3u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0xABCDEF0123456789u);
  EXPECT_EQ(var->value.words[1].aval, 0x765432100F0FA5A5u);
  EXPECT_EQ(var->value.words[2].aval, 0xFEDCBA98u);
}

TEST(StreamSliceSizeSim, ParameterAndTypedefSliceSizesPackAndUnpack) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter W = 8;\n"
                       "  parameter Z = 0;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  logic [15:0] r, z;\n"
                       "  logic [7:0] a, b;\n"
                       "  initial begin\n"
                       "    r = {<< W {16'hABCD}};\n"
                       "    {<< nib_t {a}} = 8'hAB;\n"
                       "    {<< W {b}} = 8'hAB;\n"
                       "    $display(\"%h %h %h\", r, a, b);\n"
                       "    z = {<< Z {16'hABCD}};\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "cdab ba ab\n");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "slice_size for streaming operator must be positive", 12, "11.4.14.2"));
}

TEST(StreamSliceSizeSim, SizedBasedAndUnbasedLiteralSliceSizesSliceByValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int x, a, b, c, d;\n"
                       "  initial begin\n"
                       "    x = 32'h11223344;\n"
                       "    a = {<< 8'd8 {x}};\n"
                       "    b = {<< 'h8 {x}};\n"
                       "    c = {<< 4'b1000 {x}};\n"
                       "    d = {<< '1 {x}};\n"
                       "    $display(\"%h %h %h %h\", a, b, c, d);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "44332211 44332211 44332211 22cc4488\n");
}

}  // namespace
