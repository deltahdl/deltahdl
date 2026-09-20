#include <gtest/gtest.h>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "lexer/token.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(OperatorSim, BinaryWildcardEq) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 ==? 8'd5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryWildcardNeq) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !=? 8'd3);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EvalOp, WildcardEqMismatch) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, WildcardNeqSame) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §11.4.6: an x or z in the left operand is not a wildcard for !=? either. The
// !=? operator negates a known result but passes an unknown through, so a left
// operand x at a non-wildcarded position makes !=? yield 1'bx. Driven from a
// 4-state source literal.
TEST(OperatorSim, WildcardNeqLhsXNotUnderWildcardYieldsXAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01x1;\n"
      "    b = 4'b0101;\n"
      "    r = (a !=? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

// §11.4.6: when the right operand wildcards the only differing bit position,
// the operands are treated as equal, so !=? yields a known 1'b0 -- the negated
// counterpart of the ==? wildcard-match case. The x wildcard reaches the right
// operand through a 4-state source literal.
TEST(OperatorSim, WildcardNeqRhsWildcardMatchYieldsZeroAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b0111;\n"
      "    b = 4'b01x1;\n"
      "    r = (a !=? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 0u);
}

TEST(EvalOp, WildcardEqResultIsOneBit) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(EvalOp, WildcardNeqResultIsOneBit) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kBangEqQuestion,
                          MakeInt(f.arena, 5), MakeInt(f.arena, 3));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(OperatorSim, WildcardEqWithXLiteral) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic r;\n"
      "  initial r = (4'b0101 ==? 4'b01x1);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.4.6: operands of unequal bit length are extended the same way as for the
// logical equality operators (the extension machinery supplied by §11.4.5). The
// operand widths come from real declarations so the whole extend-then-compare
// path is exercised, not a hand-built vector. The narrow right operand is
// zero-extended; its extended high bits are plain zeros (not wildcards), so a
// set high bit on the wide left operand makes ==? report a known 0.
TEST(OperatorSim, WildcardEqUnequalWidthExtendsNarrowOperand) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    wide = 8'b00010101;\n"
      "    narrow = 4'b0101;\n"
      "    r = (wide ==? narrow);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 0u);
}

// §11.4.6: with the wide operand's high bits clear, the zero-extended narrow
// operand matches across the full width and ==? reports a known 1. Driven end
// to end from declared operands of unequal width.
TEST(OperatorSim, WildcardEqUnequalWidthMatchesAfterExtension) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    wide = 8'b00000101;\n"
      "    narrow = 4'b0101;\n"
      "    r = (wide ==? narrow);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

// §11.4.6: the same unequal-length extension applies to !=?. The zero-extended
// narrow operand differs from the wide operand's set high bit, so !=? reports a
// known 1. Operand widths come from real declarations.
TEST(OperatorSim, WildcardNeqUnequalWidthExtendsNarrowOperand) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    wide = 8'b00010101;\n"
      "    narrow = 4'b0101;\n"
      "    r = (wide !=? narrow);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardNeqWithXLiteral) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic r;\n"
      "  initial r = (4'b1101 !=? 4'b01x1);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.4.6: x and z bits in the LEFT operand are not wildcards. When the left
// operand holds an x at a position the right operand does not wildcard, the
// relation is unknown and ==? yields 1'bx -- the behavior that distinguishes
// ==? from === (which never yields x). The x reaches the operand through a
// 4-state literal stored in a declared variable, so the source-through-run
// pipeline is exercised rather than a hand-built vector.
TEST(OperatorSim, WildcardEqLhsXNotUnderWildcardYieldsXAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01x1;\n"
      "    b = 4'b0101;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  // An unknown result is flagged by the low bval bit being set.
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

// §11.4.6: an x in the left operand does NOT make the result unknown when the
// corresponding right-operand bit is a wildcard. Here the right operand
// wildcards the same position, masking the left operand's x; the remaining bits
// compare equal so ==? yields a known 1'b1 -- unlike ==, which would yield x
// for the same operands. Driven end to end from 4-state literals.
TEST(OperatorSim, WildcardEqLhsXUnderRhsWildcardIsKnownAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01x1;\n"
      "    b = 4'b01x1;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

// §11.4.6: bit positions the right operand does not wildcard are compared as in
// logical equality. A differing non-wildcard bit forces a false result even
// when another position is wildcarded, so ==? yields a known 1'b0. The x
// wildcard reaches the right operand through a 4-state source literal.
TEST(OperatorSim, WildcardEqNonWildcardMismatchYieldsZeroAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1101;\n"
      "    b = 4'b01x1;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 0u);
}

// §11.4.6: when its operands are class handles, the wildcard equality operator
// is equivalent to the logical equality operator. A handle value carries no x
// or z bits, so ==? cannot behave as a wildcard match here -- two handles to
// the same object must compare equal, exactly as == would. Observed end to end
// rather than from a hand-set handle value.
TEST(OperatorSim, WildcardEqClassHandlesEqualAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h1;\n"
      "    C h2;\n"
      "    h1 = new;\n"
      "    h2 = h1;\n"
      "    r = (h1 ==? h2);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.4.6: two handles referring to distinct objects compare unequal under ==?
// just as they would under ==. The result is a known 0, never x.
TEST(OperatorSim, WildcardEqClassHandlesUnequalAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h1;\n"
      "    C h2;\n"
      "    h1 = new;\n"
      "    h2 = new;\n"
      "    r = (h1 ==? h2);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §11.4.6: the wildcard equality operator is equivalent to logical equality
// when one operand is the literal null. A non-null handle ==? null yields a
// known 0, matching == semantics.
TEST(OperatorSim, WildcardEqClassHandleWithNullAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h;\n"
      "    h = new;\n"
      "    r = (h ==? null);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §11.4.6: likewise the wildcard inequality operator matches logical inequality
// against the literal null. A non-null handle !=? null yields a known 1.
TEST(OperatorSim, WildcardNeqClassHandleWithNullAtRuntime) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h;\n"
      "    h = new;\n"
      "    r = (h !=? null);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.4.6: both x AND z bits in the right operand act as wildcards. Here the
// right operand carries a z at a bit position where the operands otherwise
// differ; the z wildcards that position so ==? reports a known match. The z
// reaches the operand through a 4-state source literal, exercising the whole
// pipeline rather than a hand-built vector.
TEST(OperatorSim, WildcardEqRhsZActsAsWildcardAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b0111;\n"
      "    b = 4'b01z1;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

// §11.4.6: a z bit in the LEFT operand is not a wildcard, just like an x. When
// the left operand holds a z at a position the right operand does not wildcard,
// the relation is unknown and ==? yields 1'bx. Driven end to end from a 4-state
// literal.
TEST(OperatorSim, WildcardEqLhsZNotUnderWildcardYieldsXAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01z1;\n"
      "    b = 4'b0101;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

// §11.4.6: for a chandle operand the wildcard equality operator is equivalent
// to logical equality. A default (null) chandle compared against null with ==?
// yields a known 1'b1, matching ==. Built from real chandle source and run.
TEST(OperatorSim, WildcardEqChandleEquivalenceAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  chandle c;\n"
      "  logic r;\n"
      "  initial r = (c ==? null);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

// §11.4.6: likewise !=? on a chandle matches logical inequality. A null chandle
// !=? null yields a known 1'b0.
TEST(OperatorSim, WildcardNeqChandleEquivalenceAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  chandle c;\n"
      "  logic r;\n"
      "  initial r = (c !=? null);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0u);
}

// §11.4.6: for interface-class handles the wildcard equality operator is
// equivalent to logical equality. Two interface-class handles referring to the
// same implementing object compare equal under ==?, exactly as == would report.
// The handles are set from real source (a concrete class assigned into the
// interface-class-typed variables) and the result observed after running.
TEST(OperatorSim, WildcardEqInterfaceClassHandleEquivalenceAtRuntime) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "interface class IC;\n"
      "  pure virtual function int get();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function int get(); return 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    IC a;\n"
      "    IC b;\n"
      "    C c;\n"
      "    c = new;\n"
      "    a = c;\n"
      "    b = c;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

// §11.4.6 (printed page 280): the operands are compared bit for bit, and one
// of unequal length is extended as for logical equality, so every bit of a
// 96-bit operand takes part. Two equal 96-bit values answer 1, and a pair that
// differs at bit 80 alone -- in the second 64-bit word -- answers 0. The two
// results are read together as eq * 10 + ne.
TEST(OperatorSim, WildcardEqWiderThanOneWordComparesEveryWord) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  int eq, ne, r;\n"
      "  initial begin\n"
      "    a = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    b = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    eq = (a ==? b);\n"
      "    a = 96'h0122_4567_89AB_CDEF_0011_2233;\n"
      "    ne = (a ==? b);\n"
      "    r = eq * 10 + ne;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 10u);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.6 (printed page 280): an x in the right operand is a wildcard at its
// own bit position and nowhere else, above bit 63 as below it. With the right
// operand x across bits 80 to 83, a left operand differing from it inside
// those bits alone matches, and one differing at bit 90 -- outside the
// wildcard, in the same word -- does not. Read as under * 10 + outside.
TEST(OperatorSim, WildcardEqRhsWildcardAboveBit63MasksItsOwnBitAlone) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  int under, outside, r;\n"
      "  initial begin\n"
      "    b = 96'h012x_4567_89AB_CDEF_0011_2233;\n"
      "    a = 96'h0129_4567_89AB_CDEF_0011_2233;\n"
      "    under = (a ==? b);\n"
      "    a = 96'h0523_4567_89AB_CDEF_0011_2233;\n"
      "    outside = (a ==? b);\n"
      "    r = under * 10 + outside;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 10u);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.6 (printed page 280): an x in the left operand is no wildcard, and a
// left x at a position the right operand does not wildcard makes the relation
// unknown, so ==? answers 1'bx. The x sits at bits 80 to 83, in the second
// word, against a known right operand; the result's low bval bit is set.
TEST(OperatorSim, WildcardEqLhsXAboveBit63NotUnderWildcardYieldsX) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 96'h012x_4567_89AB_CDEF_0011_2233;\n"
      "    b = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.6 (printed page 280): !=? is the negation of ==? over the same bit
// positions, so on 96-bit operands it answers 1 for a pair differing at bit 80
// alone, 0 for an equal pair, and 0 when the right operand wildcards bits 80
// to 83 and the left differs there alone. Read as ne * 100 + eq * 10 + wild.
TEST(OperatorSim, WildcardNeqWiderThanOneWordComparesEveryWord) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  int ne, eq, wild, r;\n"
      "  initial begin\n"
      "    b = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    a = 96'h0122_4567_89AB_CDEF_0011_2233;\n"
      "    ne = (a !=? b);\n"
      "    a = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    eq = (a !=? b);\n"
      "    b = 96'h012x_4567_89AB_CDEF_0011_2233;\n"
      "    a = 96'h0129_4567_89AB_CDEF_0011_2233;\n"
      "    wild = (a !=? b);\n"
      "    r = ne * 100 + eq * 10 + wild;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 100u);
  EXPECT_FALSE(f.has_errors);
}

// §11.4.5 (printed page 279), the operators §11.4.6 defers to for every bit
// the right operand does not wildcard: == and != compare the operands bit for
// bit, so a 96-bit pair equal in every word answers 1 to == and a pair that
// differs at bit 80 alone answers 0 to == and 1 to !=. Read together as
// eq_same * 100 + eq_diff * 10 + ne_diff.
TEST(OperatorSim, LogicalEqWiderThanOneWordComparesEveryWord) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [95:0] a, b;\n"
      "  int eq_same, eq_diff, ne_diff, r;\n"
      "  initial begin\n"
      "    a = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    b = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "    eq_same = (a == b);\n"
      "    a = 96'h0122_4567_89AB_CDEF_0011_2233;\n"
      "    eq_diff = (a == b);\n"
      "    ne_diff = (a != b);\n"
      "    r = eq_same * 100 + eq_diff * 10 + ne_diff;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 101u);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
