#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(OperatorSim, BinaryWildcardEq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 ==? 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryWildcardNeq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !=? 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01x1;\n"
      "    b = 4'b0101;\n"
      "    r = (a !=? b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b0111;\n"
      "    b = 4'b01x1;\n"
      "    r = (a !=? b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic r;\n"
      "  initial r = (4'b0101 ==? 4'b01x1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 0u);
}

// §11.4.6: with the wide operand's high bits clear, the zero-extended narrow
// operand matches across the full width and ==? reports a known 1. Driven end
// to end from declared operands of unequal width.
TEST(OperatorSim, WildcardEqUnequalWidthMatchesAfterExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

// §11.4.6: the same unequal-length extension applies to !=?. The zero-extended
// narrow operand differs from the wide operand's set high bit, so !=? reports a
// known 1. Operand widths come from real declarations.
TEST(OperatorSim, WildcardNeqUnequalWidthExtendsNarrowOperand) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.words[0].bval & 1u, 0u);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

TEST(OperatorSim, WildcardNeqWithXLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic r;\n"
      "  initial r = (4'b1101 !=? 4'b01x1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01x1;\n"
      "    b = 4'b0101;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01x1;\n"
      "    b = 4'b01x1;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1101;\n"
      "    b = 4'b01x1;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.4.6: two handles referring to distinct objects compare unequal under ==?
// just as they would under ==. The result is a known 0, never x.
TEST(OperatorSim, WildcardEqClassHandlesUnequalAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §11.4.6: the wildcard equality operator is equivalent to logical equality
// when one operand is the literal null. A non-null handle ==? null yields a
// known 0, matching == semantics.
TEST(OperatorSim, WildcardEqClassHandleWithNullAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h;\n"
      "    h = new;\n"
      "    r = (h ==? null);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §11.4.6: likewise the wildcard inequality operator matches logical inequality
// against the literal null. A non-null handle !=? null yields a known 1.
TEST(OperatorSim, WildcardNeqClassHandleWithNullAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module t;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    C h;\n"
      "    h = new;\n"
      "    r = (h !=? null);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b0111;\n"
      "    b = 4'b01z1;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b01z1;\n"
      "    b = 4'b0101;\n"
      "    r = (a ==? b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.width, 1u);
  EXPECT_NE(r->value.words[0].bval & 1u, 0u);
}

// §11.4.6: for a chandle operand the wildcard equality operator is equivalent
// to logical equality. A default (null) chandle compared against null with ==?
// yields a known 1'b1, matching ==. Built from real chandle source and run.
TEST(OperatorSim, WildcardEqChandleEquivalenceAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle c;\n"
      "  logic r;\n"
      "  initial r = (c ==? null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

// §11.4.6: likewise !=? on a chandle matches logical inequality. A null chandle
// !=? null yields a known 1'b0.
TEST(OperatorSim, WildcardNeqChandleEquivalenceAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle c;\n"
      "  logic r;\n"
      "  initial r = (c !=? null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
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
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* r = f.ctx.FindVariable("r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
}

}  // namespace
