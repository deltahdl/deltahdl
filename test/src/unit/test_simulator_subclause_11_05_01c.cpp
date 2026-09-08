// §11.5.1 Vector bit-select and part-select addressing, for what a select
// write must leave alone: the target's own bits outside the window, whatever
// word they live in, and the x and z those bits and the value's bits hold.
// §11.5.1 says a part-select partly out of range "shall, when written, only
// affect the bits that are in range", and the bits a select does not name are
// no more the write's to touch than the ones past the end are; §6.3.1 gives a
// 4-state vector four values per bit and §6.11.2 makes `logic` one of the
// 4-state types, so "leave alone" means the x or z stands, not that the bit
// reads 0.
//
// Every case here declares a target wider than one 64-bit word, or one holding
// x, or both, and asserts on Logic4Vec::ToString or on the words directly.
// That is the whole of the division between this file and its siblings.
// test/src/unit/test_simulator_subclause_11_05_01a.cpp holds the rest of the
// subclause's simulator cases -- the out-of-range and x/z-indexed selects, the
// indexed +: and -: forms, the selects of a concatenation, a packed structure
// and a multidimensional packed array, and the parameter and localparam
// bounds -- and every target it declares is 32 bits or fewer and is loaded
// with a known value first, so no case there can see a word boundary or an
// unknown bit. test/src/unit/test_simulator_subclause_11_05_01b.cpp is the
// other half of the clause, "The actual bit that is accessed by an address
// is, in part, determined by the declaration of acc", and declares ranges that
// do not end at zero or that ascend; every target here is [N:0], where an
// index and the bit offset it reaches are the same number, so nothing here
// depends on that rule.
//
// A case takes one of two routes, the two the siblings take. It runs a module
// source through RunAndFindVar in lib/cpp/test_fixtures/fixture_simulator.h
// and reads back the variable the select wrote, or it builds the select as
// Expr nodes with the builders in lib/cpp/test_builders/builders_ast.h and
// calls WriteBitSelect from src/simulator/statement_assign.h directly, which
// pins the answer at the one writer the blocking, compound, increment,
// expression and subroutine-body forms of an assignment all reach.

#include <string>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

// §11.5.1 lets `w[3:0] = 4'h0` affect w[3:0], and w[99:4] is not in that
// window: "only affect the bits that are in range" is said of the bits past an
// end, and the bits above a window that lies wholly inside the vector are no
// more the write's to touch. All 96 of them must still read 1.
//
// The target is `'1` and the value 4'h0 so that every 1 in the answer can only
// have come from the target and every 0 only from the value. A target of zero
// could not tell a kept high word from an erased one, both reading 0, and an
// all-ones value would make the whole answer ones and prove nothing about the
// window.
//
// The wrong answer was 36 zeros, then 60 ones, then four zeros. The writer
// read the target through Logic4Vec::ToUint64, which src/common/types.h calls
// a "numeric/boolean projection" and which returns words[0] alone, and rebuilt
// the whole 100-bit value from that one word, so w[99:64] came back cleared.
// The assertion is on ToString because ToUint64 is that same projection and
// cannot see the 36 bits in question.
TEST(ExpressionSim, PartSelectWriteKeepsTheTargetBitsAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [99:0] w;\n"
      "  initial begin\n"
      "    w = '1;\n"
      "    w[3:0] = 4'h0;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), std::string(96, '1') + "0000");
}

// The single-index arm of WriteBitSelect is a second body of code with the same
// defect, so the same rule needs asserting of it separately: a fix to the
// part-select writer alone would leave this red. §11.5.1 lets `w[0] = 1'b0`
// affect w[0]; the other 99 bits must still read 1.
//
// `'1` and a value of 0 for the reason given above
// PartSelectWriteKeepsTheTargetBitsAboveTheFirstWord: the one 0 in the answer
// is the only bit this write was entitled to produce.
//
// The wrong answer was 36 zeros, then 63 ones, then a zero -- the arm read
// `var->value.ToUint64()` and rebuilt the value from the single word it
// returned, discarding w[99:64].
TEST(ExpressionSim, BitSelectWriteKeepsTheTargetBitsAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [99:0] w;\n"
      "  initial begin\n"
      "    w = '1;\n"
      "    w[0] = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), std::string(99, '1') + "0");
}

// §6.3.1: "All bits of 4-state vectors can be independently set to one of the
// four basic values", and §6.11.2 lists `logic` among the 4-state types, whose
// values "have additional bits, which encode the x and z states". So the six
// bits §11.5.1 leaves outside the window of `a[1:0] = 2'b11` hold x, not 0,
// and `a` must read 8'bxxxxxx11.
//
// The target is 8'hxx rather than a wider or partly known value because the
// question here is the encoding alone, not the word boundary: eight bits keep
// the whole answer in one word, so a case that goes red can only have gone red
// for the x.
//
// The wrong answer was "00000011". ToUint64 masks by ~bval, reading x and z
// alike as 0, and MakeLogic4VecVal leaves every bval at zero, so the six x
// bits were projected to 0 on the way in and stored as 0 on the way out. The
// assertion has to be on ToString: comparing ToUint64 reads 8'bxxxxxx11 and
// 8'b00000011 as the same 3.
TEST(ExpressionSim, PartSelectWriteKeepsTheTargetsUnknownBitsOutsideTheWindow) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hxx;\n"
      "    a[1:0] = 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "xxxxxx11");
}

// The single-index arm again, and the same rule of §6.3.1 and §6.11.2 asserted
// of it separately because it is separate code: `a[0] = 1'b1` on an 8'hxx
// target must leave a[7:1] at x, so `a` reads 8'bxxxxxxx1.
//
// The wrong answer was "00000001", from the same ToUint64 read and
// MakeLogic4VecVal write the part-select arm performs.
TEST(ExpressionSim, BitSelectWriteKeepsTheTargetsUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hxx;\n"
      "    a[0] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "xxxxxxx1");
}

// The other direction of the same projection: the x is in the value rather
// than in the target. §6.3.1 sets a bit of a 4-state vector to one of four
// values and x is one of them, so `a[1:0] = 2'b1x` must leave a reading
// 8'b0000001x.
//
// The value is 2'b1x rather than 2'bxx so that three outcomes are three
// different strings: a writer that did nothing leaves "00000000", a writer
// that projects the value through ToUint64 leaves "00000010", and the right
// answer is "0000001x". An all-x value would make the first two agree.
//
// The wrong answer was "00000010". The x was read through
// `rhs_val.ToUint64()`, which is a distinct expression from the target read
// and could be fixed on its own, which is why this case stands apart from
// PartSelectWriteKeepsTheTargetsUnknownBitsOutsideTheWindow.
TEST(ExpressionSim, PartSelectWriteCarriesAnUnknownBitOfTheValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[1:0] = 2'b1x;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "0000001x");
}

// The value's x through the single-index arm, where the expression is
// `rhs_val.ToUint64() & 1` rather than the part-select arm's shift, and so is
// again separately fixable. `a[0] = 1'bx` must leave a reading 8'b1111111x.
//
// The target is 8'hFF, not 8'h00, so that the three outcomes are again three
// strings: nothing written leaves "11111111", the value projected leaves
// "11111110", and the right answer is "1111111x". Against a zeroed target the
// first two would both read "00000000" and the case could not say which of
// them had happened.
TEST(ExpressionSim, BitSelectWriteCarriesAnUnknownValueBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    a[0] = 1'bx;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1111111x");
}

// The window's offset within the target, asserted at WriteBitSelect itself the
// way SelectBoundaryBehavior.PartSelectPartialOOBLowEndSourceBits in
// test/src/unit/test_simulator_subclause_11_05_01a.cpp is, with neither the
// elaborator nor the lowerer in between, because the shift is a property of
// the writer every assignment form shares. §11.5.1 gives `w[71:68]` the four
// adjacent bits §11.5 calls "a group of adjacent bits" starting at offset 68,
// and 68 is past the first word.
//
// The target is zeroed and the value all ones -- the reverse of the sentinels
// in PartSelectWriteKeepsTheTargetBitsAboveTheFirstWord, and for the same
// reason read the other way round: here the question is where the ones landed,
// so every 1 in the answer must be one this write put there. Against an
// all-ones target the bits at w[7:4] would already be 1 and the modulo-64
// landing would be invisible.
//
// The wrong answer put 4'hF at w[7:4] and left w[71:68] at zero. Both
// `mask << bits.lo` and `(src & mask) << bits.lo` shift a uint64_t by 68,
// which C++ leaves undefined and which x86-64 takes modulo 64. The two
// assertions are exactly each other's opposite in that answer, so neither can
// pass by accident.
TEST(SelectBoundaryBehavior, PartSelectWriteLandsAtAnOffsetAboveTheFirstWord) {
  SimFixture f;
  auto* var = MakeVar(f, "wop", 100, 0);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "wop");
  sel->index = MakeInt(f.arena, 71);
  sel->index_end = MakeInt(f.arena, 68);

  WriteBitSelect(var, sel, MakeLogic4VecVal(f.arena, 4, 0xF), f.ctx, f.arena);
  ASSERT_GE(var->value.nwords, 2u);
  // w[71:68] are bits 7 down to 4 of the second word.
  EXPECT_EQ(var->value.words[1].aval & 0xF0u, 0xF0u);
  EXPECT_EQ(var->value.words[0].aval, 0u);
}

// The same undefined shift in the single-index arm, written in the source form
// the tree already contained and could not see: `enable[64] = 1'b1` on a
// `logic [64:0] enable` is what
// ConditionalEventIffSim.IffConditionSetAboveLow64BitsFires in
// test/src/unit/test_simulator_subclause_09_04_02_03b.cpp writes, and that
// case asserts only that a guarded body ran, which a 1 at enable[0] satisfies
// as well as a 1 at enable[64]. §11.5.1 makes index 64 of a [64:0] vector bit
// offset 64, so the 1 belongs in the second word and nowhere else.
//
// The target is 65'b0 so that the single 1 in the answer is the only bit this
// write produced. The wrong answer was words[0].aval == 1 and
// words[1].aval == 0: `uint64_t{1} << 64` is undefined and the count is taken
// modulo 64 on the host, so the 1 landed on enable[0]. The two assertions are
// that answer with the words exchanged.
TEST(SelectBoundaryBehavior, BitSelectWriteLandsAtAnOffsetAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [64:0] enable;\n"
      "  initial begin\n"
      "    enable = 0;\n"
      "    enable[64] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "enable");
  ASSERT_NE(var, nullptr);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, 1u);
  EXPECT_EQ(var->value.words[0].aval, 0u);
}

// The three rules together, which none of the cases above reaches: a window
// above the first word, holding an x, in a target whose surrounding bits must
// survive. The cases above are each one rule and localize a failure to one
// expression; this one cannot do that, because today it is red three times
// over and after a fix to any one of them it is still red. It is here for what
// it alone can show -- that the three answers compose. A deposit at offset 68
// has to write a bval into the second word, keep that word's other 32 bits,
// and keep the first word entire, and no case that fixes one rule at a time
// demonstrates that the three do not interfere.
//
// §11.5.1 gives `w[71:68] = 4'b10x1` those four bits and no others, §6.3.1 and
// §6.11.2 make the x of the value a value the bit can hold, so w[99:72] and
// w[67:0] must still read 1 and w[69] must read x. The target is `'1` and the
// value carries a 0, a 1 and an x, so each of the four written bits is
// distinguishable from the ones around it and from the others.
//
// The wrong answer was 36 zeros, then w[63:8] ones, then 4'b1001 deposited at
// w[7:4] with the x gone: the high word erased, the shift taken modulo 64, and
// the value projected, all at once.
TEST(ExpressionSim, PartSelectWriteAboveTheFirstWordCarriesUnknownBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [99:0] w;\n"
      "  initial begin\n"
      "    w = '1;\n"
      "    w[71:68] = 4'b10x1;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(),
            std::string(28, '1') + "10x1" + std::string(68, '1'));
}

}  // namespace
