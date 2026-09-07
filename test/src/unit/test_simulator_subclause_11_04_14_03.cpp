#include "fixture_simulator.h"
#include "helpers_reported_error.h"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "too few bits in stream for streaming unpack", 3,
                            "11.4.14.3"));
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

// §11.4.14.3: the unpack splits the stream "into one or more variables", and
// Syntax 11-4 makes every item of the target list a stream_expression, that is
// an expression -- so `a[3:0]` is a four-bit element: it claims four bits of
// the stream and deposits them in the four bits it names, leaving `a[7:4]`
// standing.
//
// The expected values follow from the clause alone. The target list is 4 + 8 =
// 12 bits and the source holds 16, and "if the source expression contains more
// bits than are needed, the appropriate number of bits shall be consumed from
// its left (most significant) end", so the stream is the top twelve bits of
// 16'h9ABC, namely 12'h9AB, and 4'hC is discarded. §11.4.14.2 has `>>` perform
// no re-ordering, so the leading 4'h9 goes to `a[3:0]` and the remaining 8'hAB
// to `b`. `a` therefore reads 8'hF9, its upper nibble surviving, and `b` 8'hAB.
//
// CollectStreamElements sized the element at the whole width of `a` and
// WriteStreamElement stored the slice over the whole of `a`, both resolving the
// element through ResolveLhsVariable, which walks a select down to its base and
// discards the index. `a` read 8'h9A and `b` 8'hBC: the mis-sizing moved the
// boundary between the two elements four bits to the right, so asserting the
// select alone would miss that every element after it takes the wrong slice.
// This is the blocking route, ApplyGenericBlockingAssign into
// UnpackStreamingConcatLhs.
//
// 8'hF0 and 8'h0F are sentinels that neither the right answers (8'hF9, 8'hAB)
// nor the wrong ones (8'h9A, 8'hBC) can produce, so an unpack that wrote
// nothing cannot pass here as one that wrote the bits the clause asks for.
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

// §11.4.14.3: "if more bits are needed than are provided by the source
// expression, an error shall be generated" -- and here none are. `{a[3:0], b}`
// needs 4 + 8 = 12 bits and the source supplies exactly 12, so no bits are
// consumed from either end: the stream is 12'h9AB whole, `a[3:0]` takes 4'h9
// over the low nibble of 8'hF0 and `b` takes 8'hAB, the same answers the
// wider-source case derives, reached without any surplus to drop.
//
// Because CollectStreamElements answered 16 for this list,
// UnpackStreamingConcatLhs compared 12 against 16, reported "too few bits in
// stream for streaming unpack" under §11.4.14.3 and returned having written
// nothing. An exact fit is the only shape that reads the mis-sizing as that
// spurious report; SelectElementTakesOnlyTheBitsItNames above has four bits to
// spare and so never reaches the check, which is why this case stands apart
// from it rather than folding into it.
//
// The clean run is asserted before the values because the report is this
// defect's signature: when it fires nothing is written, the targets keep the
// 8'hF0 and 8'h0F sentinels that no expected value can equal, and the value
// expectations would only restate what the diagnostic already said.
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

// §11.4.14.1 appends each stream_expression's own bit-stream to the generic
// stream -- "Each stream_expression within the stream_concatenation ... is
// converted to a bit-stream and appended to a packed array (stream) of bits" --
// so how many bits a target element claims is a question about the expression,
// and §11.5.1 answers it for an invalid address without taking the bits away:
// "if the bit-select address is invalid (it is out of bounds or has one or more
// x or z bits), then the value returned by the reference shall be x for 4-state
// and 0 for 2-state values", while saying separately that such a write "shall
// have no effect on the data stored". A value, not an absence. So `a[9]` on a
// `logic [7:0] a` is one bit of the stream that reaches nothing.
//
// 17'h1AAC3 laid out is 1_1010101_0_11000011. The list names 8 + 1 + 8 = 17
// bits and the source holds 17, an exact fit, so §11.4.14.3 consumes nothing
// from either end: `c` takes bits [16:9] = 8'hD5, `a[9]` takes bit [8] and
// deposits it nowhere, and `b` takes bits [7:0] = 8'hC3.
//
// StreamElementClaimedBits sized the element with SelectStorageBits, whose zero
// means "the select that addresses no bit of the object", so
// CollectStreamElements totalled 16 for a list that names 17 and
// BuildLeftAlignedStream dropped source bit [0] -- a truncation the exact fit
// does not authorize. A stream is left-aligned, which reverses the direction of
// the displacement the plain-concatenation lvalue suffers: the first element
// still lands on the most significant bits and it is what stands *after* the
// mis-sized element that moves. `c` read 8'hD5 either way and `b` read 8'h61,
// so `b` is the assertion that discriminates and asserting `c` alone would
// prove nothing. This is the blocking route, ApplyGenericBlockingAssign into
// UnpackStreamingConcatLhs.
//
// The sentinels are values no answer, right or wrong, produces: 8'h2B is
// neither 8'hC3 nor 8'h61, and 8'h3C is not 8'hD5. `a` standing at its 8'h1A
// therefore says the element's bit reached nothing, rather than that it reached
// the right nothing by accident.
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
  // The exact fit leaves nothing to trim and nothing missing, so §11.4.14.3
  // requires no report in either direction.
  EXPECT_FALSE(f.diag.HasErrors());
}

// The same defect reached through a part-select, which is what separates "an
// invalid select element claims one bit" from "an invalid select element claims
// the width its indices name". §11.5.1 has a part-select address "several
// contiguous bits", and of the wholly out-of-range one it says only that it
// "shall yield the value x when read and shall have no effect on the data
// stored when written" -- nothing there narrows the bits the indices name -- so
// `a[11:9]` on a `logic [7:0] a` is three bits of the stream and none of them
// reaches `a`.
//
// 19'h6ABC3 is 11010101_011_11000011: the list names 8 + 3 + 8 = 19 bits
// against a 19-bit source, so `c` takes bits [18:11] = 8'hD5, `a[11:9]` takes
// bits [10:8] = 3'b011 and deposits them nowhere, and `b` takes bits [7:0] =
// 8'hC3.
//
// `b` is again the discriminating assertion, and it separates three answers.
// Claiming nothing for the element -- SelectStorageBits' window, which is empty
// for a range wholly outside the declared bounds -- totalled 16, trimmed the
// low three source bits and read 8'h78. Claiming one bit, which a repair that
// only replaced that zero with a bit-select's width would do, totals 17, trims
// two and reads 8'hF0. Only the width the indices name reads 8'hC3, which is
// why this case stands beside the bit-select one above rather than repeating
// it. It claims SelectExprWidth's answer as StreamElementClaimedBits' answer.
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
  // The three bits addressed nothing, so the 8'h1A sentinel stands.
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 0x1Au);
}

// §11.5.1 gives the partially out-of-range part-select its own rule, and not
// the one it gives the wholly out-of-range one: such a select "shall, when
// read, return x for the bits that are out of range and shall, when written,
// only affect the bits that are in range". Which of its bits land says nothing
// about how wide the element is, since §11.4.14.1 makes a stream_expression's
// contribution its expression's bit-stream, so `a[9:6]` is four bits of the
// stream and two of them reach `a`.
//
// This is the shape the wholly out-of-bounds cases above cannot reach, because
// SelectStorageBits answers two here rather than zero: a repair that only
// replaced the zero would still size this element at two and still fail. It is
// what says the two questions were separated rather than the empty window
// patched.
//
// 20'hD5AC3 is 11010101_1010_11000011 and the list names 8 + 4 + 8 = 20 bits,
// an exact fit: `c` takes bits [19:12] = 8'hD5, `a[9:6]` takes bits [11:8] =
// 4'b1010, and `b` takes bits [7:0] = 8'hC3. Of those four bits a[9] and a[8]
// address nothing and a[7:6] takes 2'b10, so `a` goes 8'h1A -> 8'h9A; that
// write is established outside a streaming concatenation by
// ExpressionSim.PartSelectPartiallyOutOfBoundsWriteAffectsInRangeOnly in
// test/src/unit/test_simulator_subclause_11_05_01a.cpp. The slice is chosen so
// its top half and its bottom half read alike, which keeps the case a claim
// about the width the element claims of the stream rather than a claim about
// which two of the four bits the clipped window takes -- no case in test/
// settles that, since the established one writes 4'hF. `b` read 8'hB0 before,
// the element having claimed only the two bits it can write.
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
  // Only a[7:6] is in range, so the 8'h1A sentinel keeps its other six bits.
  EXPECT_EQ(va->value.ToUint64(), 0x9Au);
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

// §11.4.14.3 says what the unpack does and not when it happens, so a select
// element claims the bits it names on the nonblocking route as well.
// ScheduleStreamingConcatNba defers the very call ApplyGenericBlockingAssign
// makes on the spot, UnpackStreamingConcatLhs, so both doors share the element
// walk that was wrong: `a` read 8'h9A and `b` 8'hBC in the NBA region too,
// CollectStreamElements and WriteStreamElement having resolved `a[3:0]` through
// ResolveLhsVariable to the whole of `a`. Writing the same case with `<=` says
// the fix belongs in the unpacker both callers reach and not in one of them.
//
// Driven through the full pipeline the way
// NonblockingStreamingUnpackIntegration above is -- elaborate, lower, then run
// the scheduler -- so the update-region unpack really fires; without it the
// targets would still hold their sentinels. The derivation is that of
// SelectElementTakesOnlyTheBitsItNames: 4 + 8 = 12 bits of target drawn from
// the most significant end of 16'h9ABC give the stream 12'h9AB, `a[3:0]` takes
// 4'h9 into the low nibble of 8'hF0 for 8'hF9, and `b` takes 8'hAB. 8'hF0 and
// 8'h0F are again values no answer, right or wrong, produces.
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

// §11.4.14.3 says what the unpack does and not when it happens, so an invalid
// select element claims its bit on the nonblocking route as well.
// ScheduleStreamingConcatNba defers the very call ApplyGenericBlockingAssign
// makes on the spot, UnpackStreamingConcatLhs, so the deferred door reaches the
// same CollectStreamElements walk and the same StreamElementClaimedBits: `b`
// read 8'h61 in the update region too. Writing the case with `<=` says the fix
// belongs in the unpacker both callers reach and not in one of them, which is
// the claim NonblockingSelectElementTakesOnlyTheBitsItNames above makes for the
// in-bounds select and this one makes for the invalid one.
//
// Driven through the full pipeline -- elaborate, lower, then run the scheduler
// -- so the update-region unpack really fires; without it the targets would
// still hold their sentinels, and 8'h1A, 8'h2B and 8'h3C are values no answer
// produces. The derivation is that of
// OutOfBoundsBitSelectElementStillClaimsItsBitOfTheStream: 8 + 1 + 8 = 17 bits
// of target against a 17-bit source is an exact fit, so `c` takes 17'h1AAC3's
// bits [16:9] = 8'hD5, `a[9]` takes bit [8] and writes nowhere, and `b` takes
// bits [7:0] = 8'hC3.
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

// §11.4.14.3: if more bits are needed than the source expression provides, an
// error shall be generated. The report the collecting unpack raises names
// §11.4.14.3.
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

// §11.4.14.3: an unpack whose with-range depends on an earlier unpacked field
// is resolved on a second path that consumes the stream as it goes, and the
// report it raises when the stream runs out names the same subclause.
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

// §11.4.14.3: "if more bits are needed than are provided by the source
// expression, an error shall be generated" -- and the invalid select element is
// what decides whether more are needed. `{c, a[9], b}` names 8 + 1 + 8 = 17
// bits and 16'hD5C3 supplies sixteen, one short, so the report is required.
//
// Every other case here has the bits it needs, which is what makes this shape
// the only one that catches the suppressed report. UnpackStreamingConcatLhs
// compared the source's 16 against CollectStreamElements' 16, found nothing
// missing, and unpacked: `c` took 8'hD5 and `b` took 8'hC3, values that read as
// a clean and correct run. So the assertion is the diagnostic, and the two
// sentinels stand behind it -- the guard returns before writing anything, so
// `c` must still hold 8'h3C and `b` 8'h2B, values neither the right answers nor
// the wrong ones take.
//
// This is the mirror of the spurious report
// SelectElementSizesTheStreamByItsOwnWidth covers: the same mis-measurement,
// there inventing an error and here hiding one.
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

}  // namespace
