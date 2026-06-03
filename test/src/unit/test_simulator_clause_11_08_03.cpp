#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

// Clause 11.8.3 "Steps for evaluating an assignment". Step 1 (determine the
// right-hand side size by the assignment size rules) is owned by 11.6 and is
// exercised there. The rule owned here is step 2: once the right-hand side is
// resized to the left-hand side, the fill bits are sign extension if, and only
// if, the right-hand side type is signed; an unsigned right-hand side is
// zero-filled. ResizeToWidth carries that rule and the assignment write path
// drives it.

namespace {

// Direct observation of the production resize applying step 2 to a signed
// right-hand side: the high fill bits replicate the sign bit.
TEST(AssignEvalSteps, SignedRhsSignExtendsWhenWidened) {
  SimFixture f;
  auto val = MakeLogic4VecVal(f.arena, 8, 0xFF);
  val.is_signed = true;
  auto result = ResizeToWidth(val, 16, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0xFFFFu);
}

// Same widening, but an unsigned right-hand side gets zero fill, never sign
// extension.
TEST(AssignEvalSteps, UnsignedRhsZeroExtendsWhenWidened) {
  SimFixture f;
  auto val = MakeLogic4VecVal(f.arena, 8, 0xFF);
  val.is_signed = false;
  auto result = ResizeToWidth(val, 16, f.arena);
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x00FFu);
}

// A positive signed value still zero-fills above its sign bit, so the
// signedness only matters through the value of the sign bit.
TEST(AssignEvalSteps, SignedPositiveRhsZeroFillsAboveSignBit) {
  SimFixture f;
  auto val = MakeLogic4VecVal(f.arena, 8, 0x7F);
  val.is_signed = true;
  auto result = ResizeToWidth(val, 16, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x007Fu);
}

// "If needed" — when the right-hand side already matches the target width no
// extension happens regardless of signedness.
TEST(AssignEvalSteps, NoExtensionWhenWidthsMatch) {
  SimFixture f;
  auto val = MakeLogic4VecVal(f.arena, 8, 0xFF);
  val.is_signed = true;
  auto result = ResizeToWidth(val, 8, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

// End-to-end: assigning a signed narrower variable into a wider one runs the
// assignment-evaluation steps and sign-extends the negative value.
TEST(AssignEvalSteps, SignedSourceWidensWithSignExtensionEndToEnd) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [7:0] b;\n"
      "  logic signed [15:0] a;\n"
      "  initial begin\n"
      "    b = -1;\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 0xFFFFu);
}

// End-to-end: the same shape with unsigned operands zero-extends.
TEST(AssignEvalSteps, UnsignedSourceWidensWithZeroExtensionEndToEnd) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] b;\n"
      "  logic [15:0] a;\n"
      "  initial begin\n"
      "    b = 8'hFF;\n"
      "    a = b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 0x00FFu);
}

// Step 2 also governs values wider than one machine word, which take the
// multi-word resize path. A signed source whose sign bit sits in an upper word
// must fill every higher bit with ones across the remaining words. Here the
// source is 70 bits with only its sign bit (bit 69) set, widened to 130 bits.
TEST(AssignEvalSteps, SignedWideRhsSignExtendsAcrossWords) {
  SimFixture f;
  auto val = MakeLogic4Vec(f.arena, 70);
  val.words[1].aval = uint64_t{1} << 5;  // bit 69 = the sign bit
  val.is_signed = true;
  auto result = ResizeToWidth(val, 130, f.arena);
  EXPECT_EQ(result.width, 130u);
  EXPECT_EQ(result.words[0].aval, 0u);                    // below sign bit: zero
  EXPECT_EQ(result.words[1].aval, ~uint64_t{0} << 5);     // sign bit and above
  EXPECT_EQ(result.words[2].aval, 0x3u);                  // top word, mask 2 bits
}

// The unsigned counterpart on the same multi-word path zero-fills the upper
// words instead of sign-extending.
TEST(AssignEvalSteps, UnsignedWideRhsZeroExtendsAcrossWords) {
  SimFixture f;
  auto val = MakeLogic4Vec(f.arena, 70);
  val.words[1].aval = uint64_t{1} << 5;
  val.is_signed = false;
  auto result = ResizeToWidth(val, 130, f.arena);
  EXPECT_EQ(result.width, 130u);
  EXPECT_EQ(result.words[1].aval, uint64_t{1} << 5);  // sole set bit unchanged
  EXPECT_EQ(result.words[2].aval, 0u);                // zero-filled top word
}

}  // namespace
