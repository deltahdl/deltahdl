#include <gtest/gtest.h>

#include <optional>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

// Reads back the resolved value of a named parameter/localparam from an
// elaborated single-module design, so a fold performed at elaboration can be
// observed directly at the elaborator stage.
int64_t ResolvedParam(RtlirDesign* design, std::string_view name) {
  for (auto& p : design->top_modules[0]->params) {
    if (p.name == name) {
      EXPECT_TRUE(p.is_resolved);
      return p.resolved_value;
    }
  }
  ADD_FAILURE() << "parameter not found: " << name;
  return -1;
}

TEST(ConstEval, Countones) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b10110010)", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b00000000)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b11111111)", f)), 8);
}

TEST(ConstEval, Onehot) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00000001)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00001000)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00000000)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00010010)", f)), 0);
}

TEST(ConstEval, Onehot0) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00000001)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00000000)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00010010)", f)), 0);
}

// §20.9: a constant integer has no x or z bits, so $isunknown is a constant
// expression that evaluates to 0.
TEST(ConstEval, IsunknownConstantInt) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$isunknown(8'b10110010)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$isunknown(8'h00)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$isunknown(32'hFFFFFFFF)", f)), 0);
}

// §20.9: $countbits may be a constant expression when all arguments are
// constant. For a constant integer expression the result is the count of bits
// (within the literal's width) whose value matches one of the control_bit LSBs.
TEST(ConstEval, CountbitsConstantIntOnesAndZeros) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'b1)", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'b0)", f)), 4);
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'b1, 1'b0)", f)), 8);
}

// §20.9: duplicate control_bit entries collapse; constant int has no x or z
// bits so 'x and 'z control_bits contribute zero to the result.
TEST(ConstEval, CountbitsConstantIntDedupAndXZ) {
  EvalFixture f;
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'b1, 1'b1)", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'bx)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'bz)", f)), 0);
}

// §20.9: these functions may be used as constant expressions (per §11.2.1) as
// long as all their arguments are also constant expressions. A parameter is one
// of §11.2.1's constant-expression operands, so a parameter-valued argument
// must fold: with P resolving to 0xA5 (four one-bits), $countones(P) and
// $countbits(P,'1) both fold to 4, and $countbits(P,'0) counts the zero-bits
// within P's 32-bit constant value.
TEST(ConstEval, BitVectorFunctionsFoldWithParameterArgument) {
  EvalFixture f;
  ScopeMap scope = {{"P", 0xA5}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(P)", f), scope), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(P, 1'b1)", f), scope), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(P)", f), scope), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(P)", f), scope), 0);
  // 0xA5 within a 32-bit constant has 28 zero-bits.
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(P, 1'b0)", f), scope), 28);
}

// §20.9 negative: a bit-vector function is a constant expression only when its
// argument is one too. An unresolved (non-constant) argument must not fold, so
// const-evaluation yields no value rather than a wrong one.
TEST(ConstEval, BitVectorFunctionDoesNotFoldWithNonConstantArgument) {
  EvalFixture f;
  ScopeMap scope = {{"P", 0xA5}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(UNKNOWN)", f), scope),
            std::nullopt);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(UNKNOWN, 1'b1)", f), scope),
            std::nullopt);
}

// §20.9 + §11.2.1: a parameter is a constant-expression operand, and it takes
// the full parameter-resolution path (declaration -> resolution -> use) rather
// than the direct literal path. Built from real source: MASK resolves to 0xA5
// (four one-bits), so a localparam initialized from $countones(MASK) folds to 4
// during elaboration, and $countbits(MASK,'1) folds the same way.
TEST(ConstEval, BitVectorFunctionsFoldWithParameterArgumentEndToEnd) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter logic [7:0] MASK = 8'hA5;\n"
      "  localparam int ONES = $countones(MASK);\n"
      "  localparam int CB = $countbits(MASK, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "ONES"), 4);
  EXPECT_EQ(ResolvedParam(design, "CB"), 4);
}

// §20.9 + §11.2.1: a localparam is likewise a constant-expression operand.
// Built from real source, a localparam argument (MASK = 0xA5) drives $onehot0
// and $isunknown as constant expressions: 0xA5 has several one-bits (not
// one-hot0 -> 0) and no x/z (not unknown -> 0).
TEST(ConstEval, BitVectorFunctionsFoldWithLocalparamArgumentEndToEnd) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [7:0] MASK = 8'hA5;\n"
      "  localparam int OH0 = $onehot0(MASK);\n"
      "  localparam int UNK = $isunknown(MASK);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "OH0"), 0);
  EXPECT_EQ(ResolvedParam(design, "UNK"), 0);
}

// §20.9 negative: the expression argument to a bit-vector function shall be of
// a bit-stream type. A real is not a bit-stream type, so passing a real
// variable to $countones is rejected during elaboration. Built from real source
// so the check consults the operand's declared type.
TEST(BitVectorFunctionArgs, RejectsRealExpressionArgument) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  int c;\n"
      "  initial c = $countones(r);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the expression argument to '$countones' shall be of a bit-stream type",
      4, "20.9"));
}

// The same rule governs $isunknown's expression argument (and the rest): a real
// operand is rejected there too.
TEST(BitVectorFunctionArgs, RejectsRealArgumentToIsunknown) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  logic u;\n"
      "  initial u = $isunknown(r);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the expression argument to '$isunknown' shall be of a bit-stream type",
      4, "20.9"));
}

// §20.9, Syntax 20-10 negative: list_of_control_bits is non-empty, so
// $countbits with no control_bit after the expression violates the grammar and
// is rejected at elaboration.
TEST(BitVectorFunctionArgs, RejectsCountbitsWithoutControlBit) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  int c;\n"
      "  initial c = $countbits(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$countbits' requires at least one control_bit argument", 4, "20.9"));
}

// §20.9 positive control: an integral vector is a bit-stream type, so the same
// call shape elaborates cleanly -- the check must not flag a legal operand.
TEST(BitVectorFunctionArgs, AcceptsIntegralExpressionArgument) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  int c;\n"
      "  initial c = $countones(v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §20.9 states its rule over the expression argument of a bit-vector function
// and names no position the call may stand in. Each of the five cases below
// writes the call in one such position, and each is a position
// CheckBitVectorArgStmt in src/elaborator/elaborator_validate_queries.cpp
// reached only once it took its list of nested statements from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h. Every one
// of them elaborated clean beforehand, with a real operand left where a
// bit-stream type is required.
//
// Every case passes a real, which is the operand §20.9 rules out that a
// declaration states plainly, and each names a different one of the five
// functions Syntax 20-10 gives, so the rejection also witnesses that the
// position and the function are independent of each other.
TEST(BitVectorFunctionArgs, RejectsRealArgumentInAForStep) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; i = $countones(rv))\n"
      "      i = i + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the expression argument to '$countones' shall be of a bit-stream type",
      5, "20.9"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// The parser keeps the pass arm in Stmt::assert_pass_stmt.
TEST(BitVectorFunctionArgs, RejectsRealArgumentInAnAssertionPassStatement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real amp;\n"
      "  logic hot;\n"
      "  logic ready;\n"
      "  initial assert (ready) hot = $onehot(amp);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the expression argument to '$onehot' shall be of a bit-stream type", 5,
      "20.9"));
}

// §16.3's else arm of the same action block, kept in Stmt::assert_fail_stmt.
TEST(BitVectorFunctionArgs, RejectsRealArgumentInAnAssertionFailStatement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real gain;\n"
      "  logic clear;\n"
      "  logic go;\n"
      "  initial assert (go) else clear = $onehot0(gain);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the expression argument to '$onehot0' shall be of a bit-stream type", 5,
      "20.9"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The rule
// is static, so it holds whether the weighted draw would select the item or
// not.
TEST(BitVectorFunctionArgs, RejectsRealArgumentInARandcaseItem) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real drift;\n"
      "  logic unk;\n"
      "  initial randcase 2: unk = $isunknown(drift); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the expression argument to '$isunknown' shall be of a bit-stream type",
      4, "20.9"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions. The call carries a control_bit, so the report it draws
// is the bit-stream one rather than Syntax 20-10's requirement that
// list_of_control_bits be non-empty.
TEST(BitVectorFunctionArgs, RejectsRealArgumentInARandsequenceCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real slope;\n"
      "  int bits;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { bits = $countbits(slope, 1'b1); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the expression argument to '$countbits' shall be of a bit-stream type",
      6, "20.9"));
}

}  // namespace
