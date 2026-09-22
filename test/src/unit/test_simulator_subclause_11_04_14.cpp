#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_stream_unpack_ab.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// Runs the full pipeline on `src`, which streams into the byte queue `q`, then
// checks the resized queue holds exactly two elements with the given values.
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
  // §11.4.14: the streaming operators pack bit-stream operands into a
  // sequence of bits in a user-specified order. `>>` emits the operands in
  // left-to-right order, with the first element occupying the most
  // significant bits of the packed result.
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
  // §11.4.14: when a streaming_concatenation appears on the LHS, the
  // operators perform the inverse of packing, splitting the source stream
  // back into the listed targets.
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
  // §11.4.14: when the fixed-size target is wider than the streamed source,
  // the stream is widened by filling zero bits on the right (LSB side) — i.e.
  // the stream lands in the high-order bits of the target.
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
  // §11.4.14: assigning a streaming-concat source to a fixed-size target that
  // is narrower than the stream shall be an error.
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
  // §11.4.14: a dynamically sized target is first resized to the smallest
  // element count that is at least as wide as the stream, then receives the
  // stream bits left-aligned. A 16-bit stream packed into a `byte` queue
  // yields two 8-bit elements with the first byte at the MSB.
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
  // §11.4.14: when the resized dynamic target is wider than the stream, the
  // stream is widened with zero bits on the right (LSB side) before unpack —
  // a 12-bit stream packed into a `byte` queue produces two elements whose
  // combined 16 bits = stream << 4.
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
  // §11.4.14: the dynamically sized target rule names both a queue and a
  // dynamic array. Exercising the dynamic-array form: a 16-bit stream packed
  // into a `byte` dynamic array resizes it to the smallest element count that
  // is at least as wide as the stream (two), then left-aligns the bits so the
  // first element carries the most significant byte. Observed through
  // language-level reads (.size and indexed access) rather than the backing
  // store, so the test sees exactly what SystemVerilog code would.
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
  // §11.4.14: when any packed datum carries 4-state values, the resulting
  // stream is 4-state. Observable as an X bit in a `logic` source surviving
  // the pack into a `logic` target.
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
  // §11.4.14: when nothing packed is 4-state, the pack produces a 2-state
  // stream. Packing only `bit` (2-state) operands therefore yields a fully
  // known result — production fabricates no unknown bits — observed even
  // through a 4-state target that could otherwise have carried x/z.
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

// §11.4.14: a fixed-size target narrower than the stream the source produces
// is an error, and the report names §11.4.14 -- the subclause that states the
// widening rules for a bit-stream target.
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

// §11.4.14 (printed page 291): the stream initializing a block-local
// declaration is left-aligned in it as one assigned by a statement is, the
// 96-bit `{<< 32 {a, b, c}}` of three ints -- c, b, a from the left once the
// 32-bit slices are reversed -- widened with 32 zero bits on the right of a
// `bit [127:0]`: 128'h00000003_00000002_00000001_00000000, whose upper word
// (bits 127:64) is 64'h00000003_00000002 and lower word 64'h00000001_00000000.
// This is the suite's 11.4.14.3--unpack_stream_pad-sim.sv (#4362); the
// initializer was taken as evaluated and the stream sat right-aligned, upper
// word 3 and lower word 64'h00000002_00000001. The result is copied to a
// module variable the case reads, the local being gone with its block.
TEST(StreamingOperatorSim,
     DeclarationInitializerStreamIsLeftAlignedInAWiderLocal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "  bit [127:0] out;\n"
      "  initial begin\n"
      "    bit [127:0] d = {<< 32 {a, b, c}};\n"
      "    out = d;\n"
      "  end\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, uint64_t{0x00000003} << 32 | 0x00000002);
  EXPECT_EQ(var->value.words[0].aval, uint64_t{0x00000001} << 32);
}

// §11.4.14 (printed page 291) with §11.4.14.3's own example `int j = {>>{ a,
// b, c }}`, marked an error for j's 32 bits being fewer than the stream's 96:
// the declaration's initializer is reported as the statement form above is,
// at the stream, under §11.4.14. This is the suite's
// 11.4.14.3--unpack_stream_inv.sv (#4364), accepted before.
TEST(StreamingOperatorSim,
     DeclarationInitializerStreamWiderThanTheLocalErrors) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "  initial begin\n"
      "    int d = {<<{a, b, c}};\n"
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

// §11.4.14 (printed page 291) with §6.8: a module-scope declaration's
// initializer is assigned as from an initial procedure, so its stream is
// left-aligned as the block-local one above is: the same 128 bits.
// Lowerer::LowerVarInit evaluated the stream under the declared width, which
// left it right-aligned.
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

}  // namespace
