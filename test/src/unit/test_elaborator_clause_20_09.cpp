#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_evaluator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

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

}  // namespace
