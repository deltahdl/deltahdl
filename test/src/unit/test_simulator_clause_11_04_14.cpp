#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(StreamingOperatorSim, PackProducesUserSpecifiedOrder) {
  // §11.4.14: the streaming operators pack bit-stream operands into a
  // sequence of bits in a user-specified order. `>>` emits the operands in
  // left-to-right order, with the first element occupying the most
  // significant bits of the packed result.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] dst;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'h12;\n"
      "    b = 8'h34;\n"
      "    dst = {>> {a, b}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234u);
}

TEST(StreamingOperatorSim, LhsStreamingConcatUnpacks) {
  // §11.4.14: when a streaming_concatenation appears on the LHS, the
  // operators perform the inverse of packing, splitting the source stream
  // back into the listed targets.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] src;\n"
      "  initial begin\n"
      "    src = 16'hABCD;\n"
      "    {>> {a, b}} = src;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(vb->value.ToUint64(), 0xCDu);
}

TEST(StreamingOperatorSim, TargetWiderThanStreamZeroPadsOnRight) {
  // §11.4.14: when the fixed-size target is wider than the streamed source,
  // the stream is widened by filling zero bits on the right (LSB side) — i.e.
  // the stream lands in the high-order bits of the target.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] dst;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    dst = {>> {a}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
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
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StreamingOperatorSim, QueueTargetResizesToFitStream) {
  // §11.4.14: a dynamically sized target is first resized to the smallest
  // element count that is at least as wide as the stream, then receives the
  // stream bits left-aligned. A 16-bit stream packed into a `byte` queue
  // yields two 8-bit elements with the first byte at the MSB.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  logic [15:0] src;\n"
      "  initial begin\n"
      "    src = 16'hABCD;\n"
      "    q = {>> {src}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* queue = f.ctx.FindQueue("q");
  ASSERT_NE(queue, nullptr);
  ASSERT_EQ(queue->elements.size(), 2u);
  EXPECT_EQ(queue->elements[0].ToUint64(), 0xABu);
  EXPECT_EQ(queue->elements[1].ToUint64(), 0xCDu);
}

TEST(StreamingOperatorSim, QueueTargetZeroPadsRemainderOnRight) {
  // §11.4.14: when the resized dynamic target is wider than the stream, the
  // stream is widened with zero bits on the right (LSB side) before unpack —
  // a 12-bit stream packed into a `byte` queue produces two elements whose
  // combined 16 bits = stream << 4.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte q[$];\n"
      "  logic [11:0] src;\n"
      "  initial begin\n"
      "    src = 12'hABC;\n"
      "    q = {>> {src}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* queue = f.ctx.FindQueue("q");
  ASSERT_NE(queue, nullptr);
  ASSERT_EQ(queue->elements.size(), 2u);
  EXPECT_EQ(queue->elements[0].ToUint64(), 0xABu);
  EXPECT_EQ(queue->elements[1].ToUint64(), 0xC0u);
}

TEST(StreamingOperatorSim, FourStateBitsPreservedThroughPack) {
  // §11.4.14: when any packed datum carries 4-state values, the resulting
  // stream is 4-state. Observable as an X bit in a `logic` source surviving
  // the pack into a `logic` target.
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
}

TEST(StreamingOperatorSim, BitStreamCastOfStreaming) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = int'({>> {a}});\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

}  // namespace
