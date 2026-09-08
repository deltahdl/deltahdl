// §11.5.1 Vector bit-select and part-select addressing, for what a select
// must not lose: on the write side the target's own bits outside the window,
// whatever word they live in, and the x and z those bits and the value's bits
// hold; on the read side the state of the very bit the select names.
// §11.5.1 says a part-select partly out of range "shall, when written, only
// affect the bits that are in range", and the bits a select does not name are
// no more the write's to touch than the ones past the end are; §6.3.1 gives a
// 4-state vector four values per bit and §6.11.2 makes `logic` one of the
// 4-state types, so "leave alone" means the x or z stands, not that the bit
// reads 0.
//
// Every case here declares a target wider than one 64-bit word, or one holding
// x, or both, and asserts on Logic4Vec::ToString or on the words directly.
// That is the whole of the division between this file and its siblings, and
// the cases asserting on Logic4Vec::ToUint64 are the exception #3537 asks for.
// They are narrow and known, and can be, because what they hold is not
// a bit outside a word or an unknown one but where a write lands at all: they
// pin the writer's answer to §11.5.1 across the fold of its own walk of the
// clause onto SelectStorageBits, and they belong beside the writer's other
// cases rather than with the reads in the siblings.
// test/src/unit/test_simulator_subclause_11_05_01a.cpp holds the rest of the
// subclause's simulator cases -- the out-of-range and x/z-indexed selects, the
// indexed +: and -: forms, the selects of a concatenation, a packed structure
// and a multidimensional packed array, and the parameter and localparam
// bounds -- and every target it declares is 32 bits or fewer and is loaded
// with a known value first, so no case there can see a word boundary or an
// unknown bit. test/src/unit/test_simulator_subclause_11_05_01b.cpp is the
// other half of the clause, "The actual bit that is accessed by an address
// is, in part, determined by the declaration of acc", and declares ranges that
// do not end at zero or that ascend; every other target here is [N:0], where
// an index and the bit offset it reaches are the same number, so nothing else
// here depends on that rule. BitSelectWriteTakesAnAscendingDeclarationsBits is
// the one case here that does, and it is here rather than there because what
// it holds to the declaration is the writer.
//
// A case takes one of two routes, the two the siblings take. It runs a module
// source through RunAndFindVar in lib/cpp/test_fixtures/fixture_simulator.h
// and reads back the variable the select wrote, or it builds the select as
// Expr nodes with the builders in lib/cpp/test_builders/builders_ast.h and
// calls WriteBitSelect from src/simulator/statement_assign.h directly, which
// pins the answer at the one writer the blocking, compound, increment,
// expression and subroutine-body forms of an assignment all reach.
//
// The cases through the middle of the file are all writes. The reads at the
// end are §6.3.1 and the word boundary asked of the other direction, of
// EvalSelect in src/simulator/eval_select.cpp rather than of the writer:
// §11.5.1 gives a bit-select the value of the bit it addresses, so a
// bit-select of a bit holding x is 1'bx, one of a bit holding z is 1'bz, and
// one at an offset of 64 or more is still the bit at that offset. They sit
// here rather than with the other reads in the siblings for the reason every
// case here does -- each needs a target holding x or z, or one wider than a
// 64-bit word, which is what those files' targets are defined not to be.

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

// §7.4.1 makes one index of a packed multidimensional array an element of the
// inner dimension rather than a bit, so `p[2]` of a `logic [3:0][7:0] p` is
// eight bits, and §11.5.1 leaves it to the declaration which eight: the
// declared outer range is [3:0], its right-hand bound 0 is its least
// significant element, and index 2 therefore sits two elements above that end,
// at bit offset 2 * 8 == 16. `p[2] = 8'hA5` on a zeroed target must leave the
// whole 32 bits reading 32'h00A5_0000 -- A5 in the third byte up and zeros
// everywhere else.
//
// The assertion is on the whole variable rather than on a read back of `p[2]`,
// because a read taken through the same wrong window would agree with a wrong
// write and the pair would still be green; the 32 bits fit one word and hold
// no x, so ToUint64 says everything ToString would about where the byte went.
//
// The window the write took is then read off SelectStorageBits for that same
// select, built here over the variable the run left behind. src/simulator/
// statement_assign.cpp resolves §11.5.1 twice -- once in SelectStorageBits,
// which returns the window, and once in WriteBitSelectBits, which walks the
// same four arms and deposits as it goes -- and the packed-element arm is the
// one place the two are known to differ, TryWritePackedElement carrying an
// `off < var->value.width` guard the resolver's arm has not got. Both are
// right about this select today, so this case is green before the fold and
// after it; what it is for is the fold itself. It goes red if the folded
// writer resolves the element against BitSelectRange instead of DeclaredRange
// -- the flattened view would make index 2 bit offset 2 and leave 32'h000000A5
// once the width collapsed to one -- or if dropping that guard moves the
// deposit off the element, either of which parts the stored value from the
// window the resolver still names.
TEST(SelectBoundaryBehavior, PackedElementWriteAgreesWithItsStorageBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0][7:0] p;\n"
      "  initial begin\n"
      "    p = 32'h0;\n"
      "    p[2] = 8'hA5;\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);

  auto* elem = f.arena.Create<Expr>();
  elem->kind = ExprKind::kSelect;
  elem->base = MakeId(f.arena, "p");
  elem->index = MakeInt(f.arena, 2);
  auto bits = SelectStorageBits(*var, elem, f.ctx, f.arena);
  EXPECT_EQ(bits.lo, 16u);
  EXPECT_EQ(bits.width, 8u);

  auto stored = var->value.ToUint64();
  EXPECT_EQ(stored, uint64_t{0x00A50000});
  // The same 32 bits split at the window the resolver named: A5 inside it and
  // nothing at all outside it.
  auto window = ((uint64_t{1} << bits.width) - 1) << bits.lo;
  EXPECT_EQ(stored & window, uint64_t{0xA5} << bits.lo);
  EXPECT_EQ(stored & ~window, uint64_t{0});
}

// §11.5.1: "the actual bit that is accessed by an address is, in part,
// determined by the declaration of acc". `logic [0:7] asc` ascends, so its
// right-hand bound 7 names its least significant bit -- the reading §11.5.1
// fixes for its own `logic [0:31] b_vect`, whose `b_vect[0 +: 8]` it gives as
// `b_vect[0:7]`, counting up the declaration from the significant end. Index 6
// therefore sits one place above the least significant bit, and `asc[6] =
// 1'b1` on a zeroed target must leave asc reading 8'h02.
//
// An ascending declaration is where a resolution that ignored the declaration
// would part from one that honours it: taken as [7:0], index 6 would be bit
// offset 6 and the answer 8'h40. Every other target in this file is [N:0],
// where the two readings agree on every index and a writer resolving against
// the flattened [width-1:0] view would pass regardless, so this is the only
// case here that can tell them apart. The target is zeroed so the single 1 in
// the answer is the only bit this write was entitled to produce, and eight
// known bits in one word make ToUint64 the whole of the answer.
//
// Both walks of the clause honour the declaration today -- the writer through
// Variable::BitSelectRange, the resolver through the same call -- so this is
// green before the fold as well as after; it is red if the fold leaves the
// single-index arm resolving an index as an offset.
TEST(SelectBoundaryBehavior, BitSelectWriteTakesAnAscendingDeclarationsBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [0:7] asc;\n"
      "  initial begin\n"
      "    asc = 8'h00;\n"
      "    asc[6] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "asc");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), uint64_t{0x02});
}

// §11.5.1 gives an invalid address one answer on the write side: a select whose
// address carries x or z "shall have no effect on the data stored when
// written". An indexed part-select has two expressions and the clause does not
// privilege one of them, so an unknown width invalidates the address exactly as
// an unknown base does.
//
// Only one of the two was tested for. The blocking writer resolved §11.5.1 by
// its own walk and checked the base alone, running its width through
// SelectBoundValue and depositing at whatever that read; SelectStorageBits,
// which every other writer resolves through, checks both. So the same statement
// stored bits through a blocking assignment and stored none through a
// nonblocking one, a continuous assignment or a declaration initializer. That
// is the divergence folding the writer onto the resolver removes, and this is
// the case that says which of the two answers survived: the clause's.
//
// The target is given a known value first, so leaving it at 8'hC3 is the write
// having had no effect rather than the variable never having been written at
// all, and w is 4-state so that an x reaches the width at all.
TEST(SelectBoundaryBehavior, PartSelectWithAnUnknownWidthBoundWritesNothing) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] tgt;\n"
      "  logic [3:0] w;\n"
      "  initial begin\n"
      "    tgt = 8'hC3;\n"
      "    w = 4'bxxxx;\n"
      "    tgt[0 +: w] = 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f, "tgt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), uint64_t{0xC3});
}

// §11.5.1 gives a bit-select "the value of the bit" it addresses, and §6.3.1
// says "all bits of 4-state vectors can be independently set to one of the
// four basic values", x among them. So a bit-select of a bit holding x is
// 1'bx. The sharpest way to say that is not to assert on the bit-select alone
// but against the part-select spelling of the very same window in the very
// same run: `a[0]` and `a[0:0]` name one bit of one variable, and §11.5.1
// gives them the same answer or the clause has two readings. Today they
// disagree.
//
// The two spellings reach two bodies of code. `a[0:0]` carries an index_end,
// so EvalSelect routes it to EvalPackedPartSelect and on to ExtractBitField in
// src/common/types.cpp, which copies aval and bval a bit at a time and so
// keeps the x. `a[0]` falls through to the function's last statement, which
// reads the target through Logic4Vec::ToUint64 -- the "numeric/boolean
// projection" of src/common/types.h, returning `aval & ~bval` -- and rebuilds
// the answer with MakeLogic4VecVal, which sets no bval at all. The x is
// projected to 0 going in and cannot be encoded going out.
//
// The wrong answer is bit_sel "0" against part_sel "x". The assertion has to
// be on Logic4Vec::ToString: ToUint64 is the very projection under test and
// reads 1'bx and 1'b0 alike as 0, so a case comparing the two spellings
// through it would be green today. ToString is what the rest of this file
// uses, and for a one-bit result it is a one-character string that names the
// state outright.
TEST(SelectBoundaryBehavior, BitSelectOfAnUnknownBitAgreesWithThePartSelect) {
  SimFixture f;
  auto* bit_sel = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic bit_sel;\n"
      "  logic part_sel;\n"
      "  initial begin\n"
      "    a = 8'bxxxxxxxx;\n"
      "    bit_sel = a[0];\n"
      "    part_sel = a[0:0];\n"
      "  end\n"
      "endmodule\n",
      f, "bit_sel");
  ASSERT_NE(bit_sel, nullptr);
  auto* part_sel = f.ctx.FindVariable("part_sel");
  ASSERT_NE(part_sel, nullptr);
  // The part-select spelling is the one that is right today, so pinning it
  // first says that the case's own premise holds before it accuses the other.
  EXPECT_EQ(part_sel->value.ToString(), "x");
  EXPECT_EQ(bit_sel->value.ToString(), "x");
  EXPECT_EQ(bit_sel->value.ToString(), part_sel->value.ToString());
}

// z is the fourth of §6.3.1's values and is no more the projection's to lose
// than x is, so §11.5.1 gives a bit-select of a bit holding z the answer 1'bz.
// It needs asserting apart from the x because x and z are one encoding apart
// and a fix could produce the wrong one of them: src/simulator/
// evaluation_literal.cpp:93-96 stores x as (aval=1, bval=1) and z as (aval=0,
// bval=1), and Logic4Vec::ToString in src/common/types.cpp reads bval set with
// aval set as x and bval set with aval clear as z. A rebuild that set bval
// from the source but took aval from ToUint64's `aval & ~bval` -- which is 0
// for x and for z alike -- would answer z here and z again for the x above.
//
// So this case asserts the two words as well as the string. ToString says
// which of the four states the bit is in, and the words say it in the one
// encoding the rest of the simulator reads, so neither can be satisfied by a
// coincidence of the other.
//
// The wrong answer is "0": ToUint64 masks by ~bval, so the z reads 0 going in,
// and MakeLogic4VecVal leaves bval clear, so the result is a known 0 rather
// than a bit in any unknown state at all.
TEST(SelectBoundaryBehavior, BitSelectOfAHighImpedanceBitReturnsZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic bit_sel;\n"
      "  initial begin\n"
      "    a = 8'bzzzzzzzz;\n"
      "    bit_sel = a[0];\n"
      "  end\n"
      "endmodule\n",
      f, "bit_sel");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "z");
  // z is (aval=0, bval=1). An answer of x would set both and an answer of a
  // known 0 would set neither, so this pair excludes the two ways of being
  // wrong that ToString's single character already names.
  EXPECT_EQ(var->value.words[0].aval & 1u, 0u);
  EXPECT_EQ(var->value.words[0].bval & 1u, 1u);
}

// The other half of the same statement, which is wrong for a reason that has
// nothing to do with x or z: Logic4Vec::ToUint64 returns words[0] alone, so
// the bit-select arm cannot see a bit that lives in any other word. §11.5.1
// makes index 64 of a `logic [99:0]` bit offset 64, which is bit 0 of the
// second word, and the arm shifts its one word right by 64 to reach it --
// a shift by the width of the type, which C++ leaves undefined and which
// x86-64 takes modulo 64, so the shift is by 0 and the answer is bit 0 of the
// first word instead.
//
// The target is `100'h1_0000_0000_0000_0000`, one bit set at offset 64 and
// nothing else, and the case reads both w[64] and w[0]. That pairing is what
// makes the aliasing visible rather than merely a wrong bit: today the two
// selects return the same thing, and the clause says they must not, because
// the bits they name hold different values. A target with bit 0 also set, or
// an all-ones target, would have the two agreeing legitimately and the case
// would pass while reading the wrong word.
//
// The literal is written into the source rather than deposited by
// `w[64] = 1'b1` so that no writer stands between the declaration and the
// read; the two assertions on words pin that the value did land at offset 64
// before anything is claimed about what a select made of it.
//
// The wrong answer is hi "0" and lo "0". After the fix hi reads "1" and lo
// still reads "0".
TEST(SelectBoundaryBehavior, BitSelectAboveTheFirstWordReadsThatWordsBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [99:0] w;\n"
      "  logic hi;\n"
      "  logic lo;\n"
      "  initial begin\n"
      "    w = 100'h1_0000_0000_0000_0000;\n"
      "    hi = w[64];\n"
      "    lo = w[0];\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  ASSERT_GE(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[1].aval, uint64_t{1});
  EXPECT_EQ(var->value.words[0].aval, uint64_t{0});

  auto* hi = f.ctx.FindVariable("hi");
  auto* lo = f.ctx.FindVariable("lo");
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(hi->value.ToString(), "1");
  EXPECT_EQ(lo->value.ToString(), "0");
}

// §11.5.1: "Part-selects that are partially out of range shall, when read,
// return x for the bits that are out of range." `a[70:0]` on a `logic [7:0] a`
// names seventy-one indices, of which only a[7:0] are in range; result
// positions 8 through 70 are not, and all sixty-three of them must read x --
// including the seven that sit at position 64 and above, in the result's
// second word.
//
// The second word is where the answer is still wrong. EvalSelect's two read
// paths in src/simulator/eval_select.cpp now copy the window with
// ExtractBitField, which carries the bval plane and indexes the word each bit
// lands in, and which fills positions at or beyond the value's width with 0;
// the marking that runs after it, MarkOutOfRangeBitsX, bounds its loop at
// `b < width && b < 64` and ORs into `result->words[0]` alone. So positions 8
// through 63 are marked and positions 64 through 70 are left exactly as the
// copy left them, at a known 0. A known 0 is the one thing an out-of-range bit
// must not read: it is indistinguishable from the vector holding a 0 there.
//
// The value is 8'hA5 rather than 8'hFF or 8'h00 so that the in-range byte is
// one neither an erasure nor the marking could have produced. 1010_0101 is
// neither all ones nor all zeros, so a first word reading 0xA5 in its low byte
// says the copy ran and ran on the right eight bits, which is the premise the
// second word's assertion rests on; against an all-ones vector the byte would
// be indistinguishable from the x above it in the aval plane.
//
// The first word is right today -- 0xA5 in the low byte and x from position 8
// up, which is aval 0xFFFF_FFFF_FFFF_FFA5 and bval 0xFFFF_FFFF_FFFF_FF00 --
// and asserting it says the premise holds before the case accuses the second.
// Positions 64 through 70 are seven bits, so the second word must read aval
// 0x7F and bval 0x7F; today it reads 0x00 and 0x00, and that is the whole of
// the wrong answer.
//
// The assertion cannot go through Logic4Vec::ToUint64. src/common/types.h
// calls it a "numeric/boolean projection", it returns `aval & ~bval` so every
// x reads 0, and it returns words[0] alone, so the seven bits in question are
// not in what it answers at all.
TEST(SelectBoundaryBehavior, PartSelectHighOverhangAboveTheFirstWordReadsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [70:0] r;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    r = a[70:0];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  ASSERT_GE(var->value.nwords, 2u);
  // x is (aval=1, bval=1), so an out-of-range position sets both planes; a
  // word left at 0 in either plane is not seven x but seven known zeros.
  EXPECT_EQ(var->value.words[1].aval, uint64_t{0x7F});
  EXPECT_EQ(var->value.words[1].bval, uint64_t{0x7F});
  // The first word is the part of the overhang the marking already reaches,
  // and it is what says the copy put 8'hA5 where the clause asks.
  EXPECT_EQ(var->value.words[0].aval, uint64_t{0xFFFFFFFFFFFFFFA5});
  EXPECT_EQ(var->value.words[0].bval, uint64_t{0xFFFFFFFFFFFFFF00});
}

// The same sentence read from the other end of the vector, where the in-range
// bits and the overhang exchange words. §11.5.1's second indexed form reads
// `a[7 -: 80]` as the eighty indices 7 down to -72 -- the clause gives
// `a_vect[15 -: 8]` as `a_vect[15 : 8]`, counting the width downwards from the
// named index -- and only a[7:0] of those are in range. Index 7 is the
// select's most significant end, so those eight bits are the result's most
// significant eight, at positions 79 through 72, and the seventy-two positions
// below them are out of range and must read x.
//
// That is what this spelling can ask and the high-end one cannot: here the
// second word holds the copy's 8'hA5 at positions 72 through 79 and eight of
// the x at positions 64 through 71, so the marking has to OR into a word
// ExtractBitField has already written rather than fill an empty one. A
// widening that cleared each word before filling it would pass the high-end
// case, whose second word holds nothing but overhang, and lose the byte here.
//
// MarkOutOfRangeBitsX stops at position 63, so today positions 64 through 71
// come back a known 0 and the second word reads aval 0xA500 and bval 0x0000
// where §11.5.1 asks for aval 0xA5FF and bval 0x00FF. The first word is
// sixty-four out-of-range positions and is all x in both planes today, since
// every one of them is below the bound.
//
// The assertion is on Logic4Vec::ToString, which names all eighty positions in
// one string and so pins the in-range byte, the overhang inside the second
// word and the sixty-four x below it at once, rather than the two halves of
// one word separately. The wrong answer differs from it in exactly the eight
// characters for positions 71 through 64. ToUint64 could say none of it: it is
// the projection that reads every x as 0 and it returns words[0] alone.
TEST(SelectBoundaryBehavior, PartSelectLowOverhangAboveTheFirstWordReadsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [79:0] r;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    r = a[7 -: 80];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  // 8'hA5 at the top, then seventy-two x. Today the eight characters just
  // below the byte read "00000000" instead, and the rest of the string is
  // already what the clause asks.
  EXPECT_EQ(var->value.ToString(), "10100101" + std::string(72, 'x'));
}

}  // namespace
