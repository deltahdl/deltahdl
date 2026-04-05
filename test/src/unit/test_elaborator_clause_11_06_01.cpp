#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

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

TEST(Elaboration, ComparisonWidthIsOneBit) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.int_val = 10;
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.int_val = 20;
  Expr cmp;
  cmp.kind = ExprKind::kBinary;
  cmp.op = TokenKind::kEqEq;
  cmp.lhs = &lhs;
  cmp.rhs = &rhs;
  EXPECT_EQ(InferExprWidth(&cmp, typedefs), 1);
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

TEST(ExpressionBitLength, MultiplicationWidthMatchesOperands) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  int result;\n"
      "  initial a = 100;\n"
      "  always_comb begin\n"
      "    result = a * 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 200u);
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

// Table 11-21: Unsized constant number → at least 32 bits.
TEST(Elaboration, UnsizedConstantWidthAtLeast32) {
  TypedefMap typedefs;
  Expr lit;
  lit.kind = ExprKind::kIntegerLiteral;
  lit.int_val = 42;
  EXPECT_GE(InferExprWidth(&lit, typedefs), 32u);
}

// Table 11-21: Sized constant number → as given.
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

// Table 11-21: op i, where op is + - ~ → L(i).
TEST(Elaboration, UnaryPlusMinusTildeWidthEqualsOperand) {
  TypedefMap typedefs;
  Expr operand;
  operand.kind = ExprKind::kIntegerLiteral;
  operand.text = "8'h0";

  for (TokenKind op : {TokenKind::kPlus, TokenKind::kMinus, TokenKind::kTilde}) {
    Expr unary;
    unary.kind = ExprKind::kUnary;
    unary.op = op;
    unary.lhs = &operand;
    EXPECT_EQ(InferExprWidth(&unary, typedefs), 8u);
  }
}

// Table 11-21: op i, where op is & ~& | ~| ^ ~^ ^~ ! → 1 bit.
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

// Table 11-21: i op j, where op is - * / % & | ^ ^~ ~^ → max(L(i),L(j)).
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

// Table 11-21: i op j, where op is === !== != > >= < <= → 1 bit.
TEST(Elaboration, AllComparisonOpsWidthIsOneBit) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.text = "16'h0";
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.text = "16'h0";

  for (TokenKind op :
       {TokenKind::kEqEq, TokenKind::kBangEq, TokenKind::kEqEqEq,
        TokenKind::kBangEqEq, TokenKind::kLt, TokenKind::kGt,
        TokenKind::kLtEq, TokenKind::kGtEq, TokenKind::kEqEqQuestion,
        TokenKind::kBangEqQuestion}) {
    Expr cmp;
    cmp.kind = ExprKind::kBinary;
    cmp.op = op;
    cmp.lhs = &lhs;
    cmp.rhs = &rhs;
    EXPECT_EQ(InferExprWidth(&cmp, typedefs), 1u);
  }
}

// Table 11-21: i op j, where op is && || -> <-> → 1 bit.
TEST(Elaboration, LogicalOpsWidthIsOneBit) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.text = "16'h0";
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.text = "16'h0";

  for (TokenKind op :
       {TokenKind::kAmpAmp, TokenKind::kPipePipe, TokenKind::kArrow,
        TokenKind::kLtDashGt}) {
    Expr binop;
    binop.kind = ExprKind::kBinary;
    binop.op = op;
    binop.lhs = &lhs;
    binop.rhs = &rhs;
    EXPECT_EQ(InferExprWidth(&binop, typedefs), 1u);
  }
}

// Table 11-21: i op j, where op is >> << >>> <<< → L(i), j is self-determined.
TEST(Elaboration, ShiftWidthIsLhsWidth) {
  TypedefMap typedefs;
  Expr lhs;
  lhs.kind = ExprKind::kIntegerLiteral;
  lhs.text = "8'h0";
  Expr rhs;
  rhs.kind = ExprKind::kIntegerLiteral;
  rhs.text = "16'h0";

  for (TokenKind op :
       {TokenKind::kLtLt, TokenKind::kGtGt, TokenKind::kLtLtLt,
        TokenKind::kGtGtGt}) {
    Expr binop;
    binop.kind = ExprKind::kBinary;
    binop.op = op;
    binop.lhs = &lhs;
    binop.rhs = &rhs;
    EXPECT_EQ(InferExprWidth(&binop, typedefs), 8u);
  }
}

// Table 11-21: i ** j → L(i), j is self-determined.
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

// Table 11-21: {i{j,...,k}} → i × (L(j)+...+L(k)).
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

// Edge case: null expression → 0.
TEST(Elaboration, NullExpressionWidthIsZero) {
  TypedefMap typedefs;
  EXPECT_EQ(InferExprWidth(nullptr, typedefs), 0u);
}

// Edge case: context width of 0 returns self-determined width.
TEST(Elaboration, ContextWidthZeroReturnsSelfDetermined) {
  TypedefMap typedefs;
  Expr lit;
  lit.kind = ExprKind::kIntegerLiteral;
  lit.int_val = 0;
  EXPECT_EQ(ContextWidth(&lit, 0, typedefs), 32u);
}

}  // namespace
