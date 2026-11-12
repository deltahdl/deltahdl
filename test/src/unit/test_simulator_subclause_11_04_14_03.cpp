#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_stream_unpack_ab.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(StreamingUnpackSim, RightShiftUnpacksMostSignificantFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial {>> {a, b, c, d}} = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xDEu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xADu);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xBEu);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 0xEFu);
}

TEST(StreamingUnpackSim, SourceWiderConsumesFromMostSignificantEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial {>> {a, b}} = 32'hABCD1234;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xCDu);
}

TEST(StreamingUnpackSim, SourceNarrowerThanTargetsErrors) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial {>> {a, b, c, d}} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "too few bits in stream for streaming unpack", 3,
                            "11.4.14.3"));
}

TEST(StreamingUnpackSim, SourceIsAnotherStreamingConcat) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial begin\n"
      "    c = 8'h12;\n"
      "    d = 8'h34;\n"
      "    {>> {a, b}} = {>> {c, d}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x12u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0x34u);
}

TEST(StreamingUnpackSim, LeftShiftByteSliceUnpackReversesBytes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial {<< byte {a, b}} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xCDu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xABu);
}

TEST(StreamingUnpackSim, FourStateStreamCastsIntoTwoStateTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] a, b;\n"
      "  logic [15:0] s;\n"
      "  initial begin\n"
      "    s = 16'hABxx;\n"
      "    {>> {a, b}} = s;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(vb->value.ToUint64(), 0x00u);
  EXPECT_EQ(vb->value.words[0].bval & 0xFFu, 0u);
}

TEST(StreamingUnpackSim, FourStateStreamPreservedInFourStateTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] s;\n"
      "  initial begin\n"
      "    s = 16'hABxx;\n"
      "    {>> {a, b}} = s;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(va->value.words[0].bval & 0xFFu, 0u);
  EXPECT_EQ(vb->value.words[0].bval & 0xFFu, 0xFFu);
}

TEST(StreamingUnpackSim, TwoStateStreamCastsIntoFourStateTarget) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  bit [15:0] s;\n"
      "  initial begin\n"
      "    s = 16'hABCD;\n"
      "    {>> {a, b}} = s;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(vb->value.ToUint64(), 0xCDu);
  EXPECT_EQ(va->value.words[0].bval & 0xFFu, 0u);
  EXPECT_EQ(vb->value.words[0].bval & 0xFFu, 0u);
}

TEST(StreamingUnpackSim, NullClassHandleTargetIsSkipped) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  logic [7:0] a, b;\n"
      "  initial {>> {h, a, b}} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xABu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xCDu);
  EXPECT_EQ(f.ctx.FindVariable("h")->value.ToUint64(), 0u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StreamingUnpackSim, SelectElementTakesOnlyTheBitsItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
      "    {>> {a[3:0], b}} = 16'h9ABC;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0xF9u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xABu);
}

TEST(StreamingUnpackSim, SelectElementSizesTheStreamByItsOwnWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
      "    {>> {a[3:0], b}} = 12'h9AB;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xF9u);
  EXPECT_EQ(vb->value.ToUint64(), 0xABu);
}

TEST(StreamingUnpackSim,
     OutOfBoundsBitSelectElementStillClaimsItsBitOfTheStream) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {>> {c, a[9], b}} = 17'h1AAC3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x1Au);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xC3u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xD5u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StreamingUnpackSim,
     WhollyOutOfBoundsPartSelectElementClaimsTheWidthItsIndicesName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {>> {c, a[11:9], b}} = 19'h6ABC3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xD5u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xC3u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x1Au);
}

TEST(StreamingUnpackSim,
     PartiallyOutOfBoundsPartSelectElementWritesOnlyItsInRangeBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {>> {c, a[9:6], b}} = 20'hD5AC3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  auto* vc = f.ctx.FindVariable("c");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(vc->value.ToUint64(), 0xD5u);
  EXPECT_EQ(vb->value.ToUint64(), 0xC3u);
  EXPECT_EQ(va->value.ToUint64(), 0x9Au);
}

TEST(StreamingUnpackSim, NonblockingStreamingUnpackIntegration) {
  SimFixture f;
  RunStreamUnpackAbcdIntoAB(f,
                            "module t;\n"
                            "  logic [7:0] a, b;\n"
                            "  initial {>> {a, b}} <= 16'hABCD;\n"
                            "endmodule\n");
}

TEST(StreamingUnpackSim, NonblockingSelectElementTakesOnlyTheBitsItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
      "    {>> {a[3:0], b}} <= 16'h9ABC;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xF9u);
  EXPECT_EQ(vb->value.ToUint64(), 0xABu);
}

TEST(StreamingUnpackSim,
     NonblockingOutOfBoundsBitSelectElementStillClaimsItsBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {>> {c, a[9], b}} <= 17'h1AAC3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0xC3u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0xD5u);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x1Au);
}

TEST(StreamingUnpackSim, ShortStreamErrorNames11_4_14_3) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] w, x, y, z;\n"
      "  initial {>> {w, x, y, z}} = 8'h5A;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "too few bits in stream", 3,
                            "11.4.14.3"));
}

TEST(StreamingUnpackSim, ShortStreamForwardResolveNames11_4_14_3) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int len;\n"
      "  logic [7:0] body[8];\n"
      "  initial {>> {len, body with [0 +: len]}} = {32'd4, 8'hAA};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "too few bits in stream", 4,
                            "11.4.14.3"));
}

TEST(StreamingUnpackSim,
     ShortStreamWithOutOfBoundsSelectElementNames11_4_14_3) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {>> {c, a[9], b}} = 16'hD5C3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "too few bits in stream", 7,
                            "11.4.14.3"));
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 0x3Cu);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 0x2Bu);
}

TEST(StreamingUnpackSim, PropertiesThroughAHandleAreUnpackedInto) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { byte x; byte y; } pair_t;\n"
      "  class C; bit [7:0] d[]; int q[$]; pair_t s; endclass\n"
      "  C h;\n"
      "  logic [15:0] w;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    {>>{h.d}} = 32'h0A0B0C0D;\n"
      "    $write(\"%0d %0d %0d \", h.d.size(), h.d[0], h.d[3]);\n"
      "    {<< byte{h.d}} = 32'h0A0B0C0D;\n"
      "    $write(\"%0d \", h.d[0]);\n"
      "    {>>{h.q}} = 64'hDEADBEEF_00000007;\n"
      "    $write(\"%0d %h \", h.q.size(), h.q[0]);\n"
      "    {>>{h.s}} = 16'h0506;\n"
      "    w = {>>{h.s}};\n"
      "    $display(\"%0d %0d %h\", h.s.x, h.s.y, w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4 10 13 13 2 deadbeef 5 6 0506\n");
}

TEST(StreamingUnpackSim, AnElementOfASignedQueueOrDynamicArrayIsSigned) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class H; int q[$]; endclass\n"
      "  int lq[$];\n"
      "  int d[];\n"
      "  bit [31:0] u;\n"
      "  H h;\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    {>>{lq}} = 64'hDEADBEEF_00000007;\n"
      "    lq.push_back(u);\n"
      "    d = new[1];\n"
      "    d[0] = u;\n"
      "    h = new;\n"
      "    {>>{h.q}} = u;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", lq[0], lq[1], lq[2], lq[2] < "
      "0,\n"
      "             d[0], h.q[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-559038737 7 -559038737 1 -559038737 -559038737\n");
}

TEST(StreamUnpackSim, HandleAndWholeArrayTargetsTakeTheirMembersAndElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C; bit [7:0] a, b; endclass\n"
                       "  C h;\n"
                       "  byte arr [2];\n"
                       "  byte m [2][2];\n"
                       "  initial begin\n"
                       "    h = new;\n"
                       "    {>> {h}} = 16'hABCD;\n"
                       "    {>> {arr}} = 16'h1234;\n"
                       "    {>> {m}} = 32'h01020304;\n"
                       "    $display(\"%h %h %h %h %h %h\", h.a, h.b, arr[0],\n"
                       "             arr[1], m[0][1], m[1][0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ab cd 12 34 02 03\n");
}

TEST(StreamingUnpackSim,
     AnUnpackWritesDeclaredPropertiesAndLeavesTheirRandomModes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class K; rand bit [7:0] x; rand bit [7:0] y; endclass\n"
                 "module m;\n"
                 "  K h;\n"
                 "  initial begin\n"
                 "    h = new;\n"
                 "    h.x.rand_mode(0);\n"
                 "    {>>{h}} = 16'h5A3C;\n"
                 "    $display(\"%h %h %0d %0d\", h.x, h.y, h.x.rand_mode(),\n"
                 "             h.y.rand_mode());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "5a 3c 0 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
