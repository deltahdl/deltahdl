#include <gtest/gtest.h>

#include <optional>
#include <string>
#include <string_view>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_param_value.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

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

TEST(ExpressionBitLength, ShiftCountIsReadAcrossEveryWordOfTheRightOperand) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam int W = 8'd1 << 96'h1_0000_0000_0000_0000;\n"
      "  localparam int V = 8'sh80 >>> 96'h1_0000_0000_0000_0000;\n",
      f);
  EXPECT_EQ(ParamValue(design, "W"), 0);
  EXPECT_EQ(ParamValue(design, "V"), -1);
}

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

TEST(ExpressionBitLength, ComparisonOperandsAreSizedToEachOtherAlone) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam [15:0] U = (8'hFF + 8'h01 > 8'h00) ? 16'd1 : 16'd2;\n"
      "  localparam [15:0] T = (8'hFF + 8'h01 + 0 > 8'h00) ? 16'd1 : 16'd2;\n",
      f);
  EXPECT_EQ(ParamValue(design, "U"), 2);
  EXPECT_EQ(ParamValue(design, "T"), 1);
}

TEST(ExpressionBitLength, SignedOperandsExtendBySignOnlyWhenAllAreSigned) {
  ElabFixture f;
  auto* design = ElaborateLocalparams(
      "  localparam logic signed [15:0] S = 8'sh80 + 8'sd0;\n"
      "  localparam logic signed [15:0] M = 8'sh80 + 8'd0;\n",
      f);
  EXPECT_EQ(ParamValue(design, "S"), -128);
  EXPECT_EQ(ParamValue(design, "M"), 128);
}

TEST(ExpressionBitLengthElaboration, ConstantConditionalTakesBothBranchesType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [11:0] P = {4'h1, (1'b1 ? 4'hF : 8'h00)};\n"
      "  localparam int Q = 1'b1 ? 4'sb1111 : 4'd0;\n"
      "  localparam int R = 1'b1 ? 4'sb1111 : 4'sd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ParamValue(design, "P"), 0x10F);
  EXPECT_EQ(ParamValue(design, "Q"), 15);
  EXPECT_EQ(ParamValue(design, "R"), -1);
}

TEST(ExpressionBitLengthElaboration, ConstantConditionalWithAnUnfoldedBranch) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 ? 5 : U", f)), 5);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("0 ? 5 : U", f)), std::nullopt);
}

}  // namespace
