#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_stream_unpack_ab.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

static void RunStreamUnpackIntoByteQueue(SimFixture& f, const std::string& src,
                                         uint64_t elem0, uint64_t elem1) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* queue = f.ctx.FindQueue("q");
  ASSERT_NE(queue, nullptr);
  ASSERT_EQ(queue->elements.size(), 2u);
  EXPECT_EQ(queue->elements[0].ToUint64(), elem0);
  EXPECT_EQ(queue->elements[1].ToUint64(), elem1);
}

TEST(StreamingOperatorSim, PackProducesUserSpecifiedOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'h12;\n"
      "    b = 8'h34;\n"
      "    dst = {>> {a, b}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234u);
}

TEST(StreamingOperatorSim, LhsStreamingConcatUnpacks) {
  SimFixture f;
  RunStreamUnpackAbcdIntoAB(f,
                            "module t;\n"
                            "  logic [7:0] a, b;\n"
                            "  logic [15:0] src;\n"
                            "  initial begin\n"
                            "    src = 16'hABCD;\n"
                            "    {>> {a, b}} = src;\n"
                            "  end\n"
                            "endmodule\n");
}

TEST(StreamingOperatorSim, TargetWiderThanStreamZeroPadsOnRight) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] dst;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    dst = {>> {a}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFF000000u);
}

TEST(StreamingOperatorSim, TargetNarrowerThanStreamErrors) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] dst;\n"
      "  logic [15:0] a;\n"
      "  initial begin\n"
      "    a = 16'hABCD;\n"
      "    dst = {>> {a}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wider than the fixed-size target", 6, "11.4.14"));
}

TEST(StreamingOperatorSim, QueueTargetResizesToFitStream) {
  SimFixture f;
  RunStreamUnpackIntoByteQueue(f,
                               "module t;\n"
                               "  byte q[$];\n"
                               "  logic [15:0] src;\n"
                               "  initial begin\n"
                               "    src = 16'hABCD;\n"
                               "    q = {>> {src}};\n"
                               "  end\n"
                               "endmodule\n",
                               0xABu, 0xCDu);
}

TEST(StreamingOperatorSim, QueueTargetZeroPadsRemainderOnRight) {
  SimFixture f;
  RunStreamUnpackIntoByteQueue(f,
                               "module t;\n"
                               "  byte q[$];\n"
                               "  logic [11:0] src;\n"
                               "  initial begin\n"
                               "    src = 12'hABC;\n"
                               "    q = {>> {src}};\n"
                               "  end\n"
                               "endmodule\n",
                               0xABu, 0xC0u);
}

TEST(StreamingOperatorSim, DynamicArrayTargetResizesToFitStream) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte dyn[];\n"
      "  logic [15:0] src;\n"
      "  int n;\n"
      "  byte e0, e1;\n"
      "  initial begin\n"
      "    src = 16'hABCD;\n"
      "    dyn = {>> {src}};\n"
      "    n = dyn.size;\n"
      "    e0 = dyn[0];\n"
      "    e1 = dyn[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* n = f.ctx.FindVariable("n");
  auto* e0 = f.ctx.FindVariable("e0");
  auto* e1 = f.ctx.FindVariable("e1");
  ASSERT_NE(n, nullptr);
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 2u);
  EXPECT_EQ(e0->value.ToUint64(), 0xABu);
  EXPECT_EQ(e1->value.ToUint64(), 0xCDu);
}

TEST(StreamingOperatorSim, FourStateBitsPreservedThroughPack) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [3:0] b;\n"
      "  logic [7:0] dst;\n"
      "  initial begin\n"
      "    a = 4'h5;\n"
      "    b = 4'b00x0;\n"
      "    dst = {>> {a, b}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
}

TEST(StreamingOperatorSim, BitStreamCastOfStreaming) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = int'({>> {a}});\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(StreamingOperatorSim, TwoStatePackProducesKnownStream) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [7:0] a, b;\n"
      "  logic [15:0] dst;\n"
      "  initial begin\n"
      "    a = 8'h12;\n"
      "    b = 8'h34;\n"
      "    dst = {>> {a, b}};\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0x1234u);
}

TEST(StreamingOperatorSim, NarrowTargetErrorNames11_4_14) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] dst;\n"
      "  logic [15:0] wide;\n"
      "  initial begin\n"
      "    wide = 16'h1234;\n"
      "    dst = {>> {wide}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wider than the fixed-size target", 6, "11.4.14"));
}

TEST(StreamingOperatorSim,
     DeclarationInitializerStreamIsLeftAlignedInAWiderLocal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "  bit [127:0] out;\n"
      "  initial begin\n"
      "    static bit [127:0] d = {<< 32 {a, b, c}};\n"
      "    out = d;\n"
      "  end\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, uint64_t{0x00000003} << 32 | 0x00000002);
  EXPECT_EQ(var->value.words[0].aval, uint64_t{0x00000001} << 32);
}

TEST(StreamingOperatorSim,
     DeclarationInitializerStreamWiderThanTheLocalErrors) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "  initial begin\n"
      "    static int d = {<<{a, b, c}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wider than the fixed-size target", 4, "11.4.14"));
}

TEST(StreamingOperatorSim,
     ModuleScopeInitializerStreamIsLeftAlignedInAWiderVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "  bit [127:0] m = {<< 32 {a, b, c}};\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, uint64_t{0x00000003} << 32 | 0x00000002);
  EXPECT_EQ(var->value.words[0].aval, uint64_t{0x00000001} << 32);
}

TEST(StreamingConcatSim, StreamLeftAlignsInEveryFixedSizeTarget) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  wire [15:0] w;\n"
                       "  wire [3:0] n;\n"
                       "  bit [15:0] m [2];\n"
                       "  struct packed { bit [15:0] f; } s;\n"
                       "  assign w = {>> {8'hAB}};\n"
                       "  assign n = {>> {8'hAB}};\n"
                       "  initial begin\n"
                       "    m[0] = {>> {8'hAB}};\n"
                       "    s.f = {>> {8'hAB}};\n"
                       "    #1 $display(\"%h %h %h\", w, m[0], s.f);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "ab00 ab00 ab00\n");
  EXPECT_GE(f.diag.ErrorCount(), 1u);
}

TEST(StreamingConcatSim, EmptyStreamAndTwoStateQueueElements) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  byte a[$], b[$];\n"
                 "  bit [7:0] q[$], u[$];\n"
                 "  initial begin\n"
                 "    b = '{1, 2};\n"
                 "    b = {>> {a}};\n"
                 "    q = {>> {8'hx1}};\n"
                 "    u = '{0, 0};\n"
                 "    {>> {u}} = 16'hxx01;\n"
                 "    $display(\"%0d %h %h %h\", b.size(), q[0], u[0], u[1]);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0 01 00 01\n");
}

}  // namespace
