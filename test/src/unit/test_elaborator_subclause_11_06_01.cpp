#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

// Module m elaborated around the localparam declarations `items`, so that
// each fold test below states the expressions it reads and their readings.
RtlirDesign* ElaborateLocalparams(std::string_view items, ElabFixture& f) {
  std::string src = "module m;\n";
  src += items;
  src += "endmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  return design;
}

TEST(Elaboration, BinaryAdditionWidthIsMaxOfOperands) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.int_val = 10;
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.int_val = 20;
  Expr binop;
  binop.kind = ExprKind::kBinary;
  binop.op = TokenKind::kPlus;
  binop.lhs = &lhs;
  binop.rhs = &rhs;
  EXPECT_EQ(InferExprWidth(&binop, typedefs), 32);
}

TEST(Elaboration, ConcatenationWidthIsSumOfElements) {
  TypedefMap typedefs;
  Expr a;
  a.kind = ExprKind::kIntegerLiteral;
  a.int_val = 1;
  Expr b;
  b.kind = ExprKind::kIntegerLiteral;
  b.int_val = 2;
  Expr concat;
  concat.kind = ExprKind::kConcatenation;
  concat.elements = {&a, &b};
  EXPECT_EQ(InferExprWidth(&concat, typedefs), 64);
}

TEST(Elaboration, ContextWidthMaxOfSelfAndContext) {
  TypedefMap typedefs;
  Expr a;
  a.kind = ExprKind::kIntegerLiteral;
  a.int_val = 0;

  EXPECT_EQ(InferExprWidth(&a, typedefs), 32u);

  EXPECT_EQ(ContextWidth(&a, 16, typedefs), 32u);

  EXPECT_EQ(ContextWidth(&a, 64, typedefs), 64u);

  EXPECT_EQ(ContextWidth(&a, 32, typedefs), 32u);
}

TEST(Elaboration, AssignmentWiderLhsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [16:0] result;\n"
      "  initial result = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, AssignmentNarrowerLhsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial result = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, TernaryExprBitLength) {
  TypedefMap typedefs;
  Expr cond;
  cond.kind = ExprKind::kIntegerLiteral;
  cond.int_val = 1;
  Expr true_e;
  true_e.kind = ExprKind::kIntegerLiteral;
  true_e.int_val = 0;
  Expr false_e;
  false_e.kind = ExprKind::kIntegerLiteral;
  false_e.int_val = 0;
  Expr tern;
  tern.kind = ExprKind::kTernary;
  tern.condition = &cond;
  tern.true_expr = &true_e;
  tern.false_expr = &false_e;

  EXPECT_EQ(InferExprWidth(&tern, typedefs), 32u);
}

TEST(Elaboration, TypeRefInferWidth) {
  Arena arena;
  auto* inner = arena.Create<Expr>();
  inner->kind = ExprKind::kIntegerLiteral;
  auto* ref = arena.Create<Expr>();
  ref->kind = ExprKind::kTypeRef;
  ref->lhs = inner;
  TypedefMap typedefs;
  EXPECT_EQ(InferExprWidth(ref, typedefs), 32u);
}

TEST(Elaboration, UnsizedConstantWidthAtLeast32) {
  TypedefMap typedefs;
  Expr lit;
  lit.kind = ExprKind::kIntegerLiteral;
  lit.int_val = 42;
  EXPECT_GE(InferExprWidth(&lit, typedefs), 32u);
}

TEST(Elaboration, SizedConstantWidthAsGiven) {
  TypedefMap typedefs;
  Expr lit8;
  lit8.kind = ExprKind::kIntegerLiteral;
  lit8.text = "8'hFF";
  EXPECT_EQ(InferExprWidth(&lit8, typedefs), 8u);

  Expr lit16;
  lit16.kind = ExprKind::kIntegerLiteral;
  lit16.text = "16'd0";
  EXPECT_EQ(InferExprWidth(&lit16, typedefs), 16u);

  Expr lit1;
  lit1.kind = ExprKind::kIntegerLiteral;
  lit1.text = "1'b0";
  EXPECT_EQ(InferExprWidth(&lit1, typedefs), 1u);
}

TEST(Elaboration, UnaryPlusMinusTildeWidthEqualsOperand) {
  TypedefMap typedefs;
  Expr operand;
  operand.kind = ExprKind::kIntegerLiteral;
  operand.text = "8'h0";

  for (TokenKind op :
       {TokenKind::kPlus, TokenKind::kMinus, TokenKind::kTilde}) {
    Expr unary;
    unary.kind = ExprKind::kUnary;
    unary.op = op;
    unary.lhs = &operand;
    EXPECT_EQ(InferExprWidth(&unary, typedefs), 8u);
  }
}

TEST(Elaboration, ReductionAndLogicalNotWidthIsOneBit) {
  TypedefMap typedefs;
  Expr operand;
  operand.kind = ExprKind::kIntegerLiteral;
  operand.text = "16'h0";

  for (TokenKind op :
       {TokenKind::kAmp, TokenKind::kTildeAmp, TokenKind::kPipe,
        TokenKind::kTildePipe, TokenKind::kCaret, TokenKind::kTildeCaret,
        TokenKind::kCaretTilde, TokenKind::kBang}) {
    Expr unary;
    unary.kind = ExprKind::kUnary;
    unary.op = op;
    unary.lhs = &operand;
    EXPECT_EQ(InferExprWidth(&unary, typedefs), 1u);
  }
}

TEST(Elaboration, ArithmeticAndBitwiseWidthIsMaxOfOperands) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.text = "8'h0";
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.text = "16'h0";

  for (TokenKind op :
       {TokenKind::kMinus, TokenKind::kStar, TokenKind::kSlash,
        TokenKind::kPercent, TokenKind::kAmp, TokenKind::kPipe,
        TokenKind::kCaret, TokenKind::kCaretTilde, TokenKind::kTildeCaret}) {
    Expr binop;
    binop.kind = ExprKind::kBinary;
    binop.op = op;
    binop.lhs = &lhs;
    binop.rhs = &rhs;
    EXPECT_EQ(InferExprWidth(&binop, typedefs), 16u);
  }
}

TEST(Elaboration, AllComparisonOpsWidthIsOneBit) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.text = "16'h0";
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.text = "16'h0";

  for (TokenKind op : {TokenKind::kEqEq, TokenKind::kBangEq, TokenKind::kEqEqEq,
                       TokenKind::kBangEqEq, TokenKind::kLt, TokenKind::kGt,
                       TokenKind::kLtEq, TokenKind::kGtEq,
                       TokenKind::kEqEqQuestion, TokenKind::kBangEqQuestion}) {
    Expr cmp;
    cmp.kind = ExprKind::kBinary;
    cmp.op = op;
    cmp.lhs = &lhs;
    cmp.rhs = &rhs;
    EXPECT_EQ(InferExprWidth(&cmp, typedefs), 1u);
  }
}

TEST(Elaboration, LogicalOpsWidthIsOneBit) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.text = "16'h0";
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.text = "16'h0";

  for (TokenKind op : {TokenKind::kAmpAmp, TokenKind::kPipePipe,
                       TokenKind::kArrow, TokenKind::kLtDashGt}) {
    Expr binop;
    binop.kind = ExprKind::kBinary;
    binop.op = op;
    binop.lhs = &lhs;
    binop.rhs = &rhs;
    EXPECT_EQ(InferExprWidth(&binop, typedefs), 1u);
  }
}

TEST(Elaboration, ShiftWidthIsLhsWidth) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.text = "8'h0";
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.text = "16'h0";

  for (TokenKind op : {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
                       TokenKind::kGtGtGt}) {
    Expr binop;
    binop.kind = ExprKind::kBinary;
    binop.op = op;
    binop.lhs = &lhs;
    binop.rhs = &rhs;
    EXPECT_EQ(InferExprWidth(&binop, typedefs), 8u);
  }
}

TEST(Elaboration, PowerWidthIsLhsWidth) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.text = "8'h0";
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.text = "16'h0";

  Expr binop;
  binop.kind = ExprKind::kBinary;
  binop.op = TokenKind::kPower;
  binop.lhs = &lhs;
  binop.rhs = &rhs;
  EXPECT_EQ(InferExprWidth(&binop, typedefs), 8u);
}

TEST(Elaboration, ReplicationWidthIsCountTimesInner) {
  TypedefMap typedefs;
  Arena arena;
  auto* count = arena.Create<Expr>();
  count->kind = ExprKind::kIntegerLiteral;
  count->int_val = 3;
  auto* elem = arena.Create<Expr>();
  elem->kind = ExprKind::kIntegerLiteral;
  elem->text = "8'h0";

  auto* repl = arena.Create<Expr>();
  repl->kind = ExprKind::kReplicate;
  repl->repeat_count = count;
  repl->elements.push_back(elem);
  EXPECT_EQ(InferExprWidth(repl, typedefs), 24u);
}

TEST(Elaboration, NullExpressionWidthIsZero) {
  TypedefMap typedefs;
  EXPECT_EQ(InferExprWidth(nullptr, typedefs), 0u);
}

TEST(Elaboration, ContextWidthZeroReturnsSelfDetermined) {
  TypedefMap typedefs;
  Expr lit;
  lit.kind = ExprKind::kIntegerLiteral;
  lit.int_val = 0;
  EXPECT_EQ(ContextWidth(&lit, 0, typedefs), 32u);
}

// §11.6.1's Table 11-21 (printed pages 299-300): a shift and a power are as
// wide as their left operand, the right being self-determined, so the fold
// cuts each to that width. `8'd2 ** 32'd8` is 256 cut to 8 bits, 0, and
// `8'd1 << 32'd8` the same 256 cut the same way; `16'd1 << 32'd8` keeps its
// 256 in 16 bits; `8'd255 << 96'd1` is 0x1FE cut to 8 bits, 0xFE. A fold
// sized by the wider operand read 256, 256 and 510 from the first, second
// and last. Each parameter is declared with neither type nor range, so its
// value is self-determined (§6.20.2, printed 126): under `int` the 32-bit
// target would size the left operand (§11.6.1, printed 299) and the four
// would read 256, 256, 256 and 510.
TEST(ExpressionBitLength, ShiftAndPowerFoldAtTheLeftOperandsWidth) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam A = 8'd2 ** 32'd8;\n"
      "  localparam B = 8'd1 << 32'd8;\n"
      "  localparam C = 16'd1 << 32'd8;\n"
      "  localparam E = 8'd255 << 96'd1;\n",
      f);
  EXPECT_EQ(ParamValue(design, "A"), 0);
  EXPECT_EQ(ParamValue(design, "B"), 0);
  EXPECT_EQ(ParamValue(design, "C"), 256);
  EXPECT_EQ(ParamValue(design, "E"), 0xFE);
}

// §11.4.10 (printed page 284): the count is an unsigned number of whatever
// size the right operand has, so a count of 2^64, whose one set bit lies
// above the low word, is at least any width and leaves nothing of the left
// operand -- 0 of `8'd1`, and the sign fill alone, 8'hFF read as -1, of the
// signed `8'sh80` under `>>>`. A fold reading the count's low word shifted
// by 0 and read 1 and -128.
TEST(ExpressionBitLength, ShiftCountIsReadAcrossEveryWordOfTheRightOperand) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam int W = 8'd1 << 96'h1_0000_0000_0000_0000;\n"
      "  localparam int V = 8'sh80 >>> 96'h1_0000_0000_0000_0000;\n",
      f);
  EXPECT_EQ(ParamValue(design, "W"), 0);
  EXPECT_EQ(ParamValue(design, "V"), -1);
}

// §11.8.1 (printed page 302): the sign of a self-determined operand is its
// own and the result is unsigned only where an operand that is not
// self-determined is, so a power is signed where its base is and a shift
// where its left operand is (§11.4.10, printed 284). `-8'sd2 ** 32'sd3` is
// (-2)^3 = -8 in 8 signed bits, `8'sd2 ** 8'd3` is 8, and `-8'sd2 ** 8'd3`
// is -8 too: a fold that asked both operands read the base as the unsigned
// 254, whose cube cut to 8 bits is 248. `-8'sd8 >> 1` is 8'hF8 shifted down
// with a zero brought in, 8'h7C = 124, signed and positive; a fold reading
// the sign-extended value at 32 bits shifted its fill into the field and
// read 0xFFFFFFFC. R is declared with neither type nor range so that its
// value is self-determined (§6.20.2, printed 126): under `int` the 32-bit
// target sizes the shifted operand and the fill is in the field by right,
// which ContextDeterminedOperandsAreSizedByTheTarget below reads.
TEST(ExpressionBitLength, PowerAndShiftTakeTheLeftOperandsSignedness) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam int F = -8'sd2 ** 32'sd3;\n"
      "  localparam int G = 8'sd2 ** 8'd3;\n"
      "  localparam int H = -8'sd2 ** 8'd3;\n"
      "  localparam R = -8'sd8 >> 1;\n",
      f);
  EXPECT_EQ(ParamValue(design, "F"), -8);
  EXPECT_EQ(ParamValue(design, "G"), 8);
  EXPECT_EQ(ParamValue(design, "H"), -8);
  EXPECT_EQ(ParamValue(design, "R"), 124);
}

// §11.6.1 (printed page 299) with §11.8.2 (printed 302): the right-hand side
// of an assignment is context-determined, sized by the largest of its
// operands and the left-hand side, and that size is propagated down to the
// context-determined operands before the operator is applied. `8'hAB << 8`
// assigned to a 16-bit target is 8'hAB extended to 16 bits, the count
// self-determined (Table 11-21), then shifted: 0xAB00. `8'hFF + 8'h01` in
// 16 bits keeps its carry, 0x100. `16'h1234 + 0` is 32 bits wide, the
// unsized 0 being 32, and the sum 0x1234 is cut to the 8-bit target, 0x34
// (§11.8.3, printed 303, and §6.20.2, printed 126). `-8'sd8 >> 1` in a
// 32-bit signed target extends 8'hF8 by its sign to 0xFFFFFFF8 -- the
// expression is signed, its one context-determined operand being signed
// (§11.8.1, printed 302) -- and the logical shift brings a zero in above
// it, 0x7FFFFFFC. Folded at the operands' own widths, the four read 0, 0,
// 0x34 and 124.
TEST(ExpressionBitLength, ContextDeterminedOperandsAreSizedByTheTarget) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam [15:0] Y = 8'hAB << 8;\n"
      "  localparam [15:0] W = 8'hFF + 8'h01;\n"
      "  localparam [7:0] V = 16'h1234 + 0;\n"
      "  localparam int R = -8'sd8 >> 1;\n",
      f);
  EXPECT_EQ(ParamValue(design, "Y"), 0xAB00);
  EXPECT_EQ(ParamValue(design, "W"), 0x100);
  EXPECT_EQ(ParamValue(design, "V"), 0x34);
  EXPECT_EQ(ParamValue(design, "R"), 0x7FFFFFFC);
}

// §11.6.2 (printed page 300): the clause's own example. `(a + b) >> 1` over
// 16-bit operands into a 16-bit target adds at 16 bits and loses the carry,
// so 16'hFFFF + 16'h0001 is 0 and the shift reads 0; adding the unsized 0
// makes the sum 32 bits wide, keeps the carry, and the shift reads 0x8000.
// The condition of a conditional and the count of a shift are
// self-determined (Table 11-21, printed 300), so the 16-bit target reaches
// neither: 1'b1 stays one bit, and the count 1 sizes nothing.
TEST(ExpressionBitLength, AddingAnUnsizedZeroWidensTheSumAsTheClauseSays) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam [15:0] LOST = (16'hFFFF + 16'h0001) >> 1;\n"
      "  localparam [15:0] KEPT = (16'hFFFF + 16'h0001 + 0) >> 1;\n"
      "  localparam [15:0] SEL = 1'b1 ? (16'hFFFF + 16'h0001 + 0) >> 1 : 0;\n",
      f);
  EXPECT_EQ(ParamValue(design, "LOST"), 0);
  EXPECT_EQ(ParamValue(design, "KEPT"), 0x8000);
  EXPECT_EQ(ParamValue(design, "SEL"), 0x8000);
}

// §11.8.2 (printed page 303): the operands of a relational operator affect
// each other as context-determined operands do and are sized to the larger
// of the two, and to nothing outside -- Table 11-21 (printed 299) sizes them
// to max(L(i), L(j)) and the operator's answer to one bit. So `8'hFF + 8'h01
// > 8'h00` written in a 16-bit target adds at 8 bits, where the sum is 0,
// and 0 > 0 is false: U takes the second arm, 2. Sized by the target, the
// sum would be 0x100, the comparison true and U 1.
TEST(ExpressionBitLength, ComparisonOperandsAreSizedToEachOtherAlone) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam [15:0] U = (8'hFF + 8'h01 > 8'h00) ? 16'd1 : 16'd2;\n"
      "  localparam [15:0] T = (8'hFF + 8'h01 + 0 > 8'h00) ? 16'd1 : 16'd2;\n",
      f);
  EXPECT_EQ(ParamValue(design, "U"), 2);
  EXPECT_EQ(ParamValue(design, "T"), 1);
}

// §11.8.2 (printed page 303): an operand extended to the propagated size is
// sign-extended if and only if the propagated type is signed, which §11.8.1
// (printed 302) makes it where every context-determined operand is. Both
// operands of `8'sh80 + 8'sd0` are signed, so 8'sh80 is extended by its sign
// to the 16-bit target, 16'hFF80, and the sum read signed is -128. With an
// unsigned operand beside it, `8'sh80 + 8'd0`, the expression is unsigned
// and 8'sh80 is zero-extended, 16'h0080 = 128, whatever the target's own
// signedness (§11.8.1: the type does not depend on the left-hand side). A
// fold extending each operand by its own sign read -128 from both.
TEST(ExpressionBitLength, SignedOperandsExtendBySignOnlyWhenAllAreSigned) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam logic signed [15:0] S = 8'sh80 + 8'sd0;\n"
      "  localparam logic signed [15:0] M = 8'sh80 + 8'd0;\n",
      f);
  EXPECT_EQ(ParamValue(design, "S"), -128);
  EXPECT_EQ(ParamValue(design, "M"), 128);
}

}  // namespace
