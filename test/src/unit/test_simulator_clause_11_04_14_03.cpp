#include "fixture_simulator.h"
#include "helpers_stream_unpack_ab.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// §11.4.14.3: a streaming_concatenation on the left of an assignment performs
// the reverse (unpack) operation, splitting the source stream back into the
// listed targets. With `>>`, the most significant source bits fill the first
// listed target. Driven end to end from real declarations so the target widths
// come from elaboration, not a hand-built simulation context.
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

// §11.4.14.3: when the source stream holds more bits than the targets need, the
// required bits are consumed from the source's most significant (left) end and
// the surplus low-order bits are discarded. Here 16 target bits are drawn from
// a 32-bit source, keeping ABCD and dropping 1234.
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

// §11.4.14.3: if the targets need more bits than the source stream supplies, an
// error shall be generated. Four bytes (32 bits) of target with only a 16-bit
// source trips the runtime diagnostic.
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
  EXPECT_TRUE(f.diag.HasErrors());
}

// §11.4.14.3: the source of an unpack may itself be another
// streaming_concatenation; the stream it produces is unpacked into the targets.
// The `>> {c, d}` source packs to 0x1234, which unpacks back into a and b.
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

// §11.4.14.3 consuming §11.4.14.2: the reverse (unpack) operation must handle a
// left-shift (`<<`) streaming target, whose stream §11.4.14.2 re-orders by the
// slice size before distributing it to the targets. Built from real `<< byte`
// source syntax and run end to end: the byte slice reverses the two source
// bytes, so the low source byte lands in the first target.
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

// §11.4.14.3: unpacking a 4-state stream into a 2-state target is done by
// casting to the 2-state type, so unknown (x) source bits collapse to 0 in the
// target. The low source byte is all-x; the `bit` target `b` becomes 0 with no
// unknown bits, while the known upper byte unpacks normally into `a`.
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
  // x bits cast away to 0 in the 2-state target, not retained as raw 1s.
  EXPECT_EQ(vb->value.ToUint64(), 0x00u);
  EXPECT_EQ(vb->value.words[0].bval & 0xFFu, 0u);
}

// §11.4.14.3: "and vice versa" — a 4-state target retains the stream's unknown
// bits rather than collapsing them, distinguishing it from the 2-state cast.
// The low source byte is all-x; the `logic` target `b` keeps those x bits set.
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
  // Known upper byte unpacks with no unknown bits.
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(va->value.words[0].bval & 0xFFu, 0u);
  // x bits retained in the 4-state target rather than cast to 0.
  EXPECT_EQ(vb->value.words[0].bval & 0xFFu, 0xFFu);
}

// §11.4.14.3: "and vice versa" — the complementary cast direction. A 2-state
// source stream unpacked into 4-state targets is cast to the 4-state type: the
// known bits transfer unchanged and no unknown bits are fabricated (bval stays
// clear), which distinguishes a genuine cast from copying a raw 4-state word.
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
  // No unknown bits appear in the 4-state targets from a 2-state source.
  EXPECT_EQ(va->value.words[0].bval & 0xFFu, 0u);
  EXPECT_EQ(vb->value.words[0].bval & 0xFFu, 0u);
}

// §11.4.14.3: a null class handle among the unpack targets is skipped — it
// consumes no stream bits, is left unmodified, and no object is created to
// receive them, so the remaining scalar targets absorb the whole stream. Built
// from real class + handle declaration syntax and run end to end: the handle is
// never `new`ed, so it stays null and the two bytes take all 16 source bits.
// Without the skip the handle would claim bits from the stream (and, being
// wider than the source, trip the too-few-bits error).
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
  // The null handle is untouched and no unpack error was raised.
  EXPECT_EQ(f.ctx.FindVariable("h")->value.ToUint64(), 0u);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §11.4.14.3: the reverse (unpack) operation applies to a streaming target of a
// nonblocking assignment as well as a blocking one. Driven through the full
// pipeline so the deferred NBA-region unpack is exercised; without it the
// targets would keep their initial value.
TEST(StreamingUnpackSim, NonblockingStreamingUnpackIntegration) {
  SimFixture f;
  RunStreamUnpackAbcdIntoAB(f,
                            "module t;\n"
                            "  logic [7:0] a, b;\n"
                            "  initial {>> {a, b}} <= 16'hABCD;\n"
                            "endmodule\n");
}

}  // namespace
