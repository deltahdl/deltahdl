#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.54 sequence expression: the VPI object model for a sequence expression.
// The sequence-expr class groups operation, sequence-instance, distribution and
// bare-expression kinds; an operation's vpiOpType is drawn from a fixed set of
// sequence operators and its operands appear in a defined order; a sequence
// instance resolves to its declaration and reports its arguments in formal
// order (filling defaults); and a bare expression exposes its match items.
// These tests observe the production helpers in vpi.cpp that apply those rules.

// D1: the sequence-expr class groups the member kinds the diagram draws -
// operation, sequence instance, distribution, and a bare boolean expression
// (modeled by the concrete expression kinds). Unrelated kinds are not members.
TEST(SequenceExprModel, ClassGroupsItsMemberKinds) {
  EXPECT_TRUE(VpiIsSequenceExprType(vpiOperation));
  EXPECT_TRUE(VpiIsSequenceExprType(vpiSequenceInst));
  EXPECT_TRUE(VpiIsSequenceExprType(vpiDistribution));
  EXPECT_TRUE(VpiIsSequenceExprType(vpiConstant));
  EXPECT_TRUE(VpiIsSequenceExprType(vpiRefObj));

  EXPECT_FALSE(VpiIsSequenceExprType(vpiModule));
  EXPECT_FALSE(VpiIsSequenceExprType(vpiNet));
  EXPECT_FALSE(VpiIsSequenceExprType(vpiClockingBlock));
}

// Detail 2: within a sequence expression vpiOpType is one of exactly these
// eleven sequence operators.
TEST(SequenceExprModel, OpTypeSetCoversTheElevenSequenceOperators) {
  for (int op :
       {vpiCompAndOp, vpiIntersectOp, vpiCompOrOp, vpiFirstMatchOp,
        vpiThroughoutOp, vpiWithinOp, vpiUnaryCycleDelayOp, vpiCycleDelayOp,
        vpiRepeatOp, vpiConsecutiveRepeatOp, vpiGotoRepeatOp}) {
    EXPECT_TRUE(VpiIsSequenceExprOpType(op)) << "op=" << op;
  }
}

// D2: an operation object reports its operation type as an int property through
// vpi_get(vpiOpType); for a sequence operation that value is one of the
// sequence operators.
TEST(SequenceExprModel, OperationReportsItsOpTypeProperty) {
  VpiContext ctx;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiThroughoutOp;

  EXPECT_EQ(ctx.Get(vpiOpType, &op), vpiThroughoutOp);
  EXPECT_TRUE(VpiIsSequenceExprOpType(ctx.Get(vpiOpType, &op)));

  // An operation with no recorded op type reports zero rather than garbage.
  VpiObject unset;
  unset.type = vpiOperation;
  EXPECT_EQ(ctx.Get(vpiOpType, &unset), 0);
}

// Detail 2 edge: operators outside the sequence set (ordinary expression ops
// and property-level operators) are rejected.
TEST(SequenceExprModel, OpTypeSetRejectsNonSequenceOperators) {
  EXPECT_FALSE(VpiIsSequenceExprOpType(vpiAddOp));
  EXPECT_FALSE(VpiIsSequenceExprOpType(vpiLogAndOp));
  EXPECT_FALSE(VpiIsSequenceExprOpType(vpiImplyOp));
  EXPECT_FALSE(VpiIsSequenceExprOpType(vpiUntilOp));
}

// Detail 3a (unary cycle delay ##): operands are sequence, left range, right
// range, in that order; the right range is dropped when it equals the left.
TEST(SequenceExprModel, UnaryCycleDelayOperandOrderAndRangeOmission) {
  VpiObject seq;
  VpiObject lo;
  VpiObject hi;

  auto with_range = VpiUnaryCycleDelayOperands(&seq, &lo, &hi);
  ASSERT_EQ(with_range.size(), 3u);
  EXPECT_EQ(with_range[0], &seq);
  EXPECT_EQ(with_range[1], &lo);
  EXPECT_EQ(with_range[2], &hi);

  // A range whose bounds coincide is given as a single bound.
  auto eq_range = VpiUnaryCycleDelayOperands(&seq, &lo, &lo);
  ASSERT_EQ(eq_range.size(), 2u);
  EXPECT_EQ(eq_range[0], &seq);
  EXPECT_EQ(eq_range[1], &lo);

  // No right range supplied at all -> sequence and left range only.
  auto no_right = VpiUnaryCycleDelayOperands(&seq, &lo, nullptr);
  ASSERT_EQ(no_right.size(), 2u);
  EXPECT_EQ(no_right[1], &lo);
}

// Detail 3b (binary cycle delay ##): operands are lhs sequence, rhs sequence,
// left range, right range; the right range is dropped when equal to the left.
TEST(SequenceExprModel, CycleDelayOperandOrderAndRangeOmission) {
  VpiObject lhs;
  VpiObject rhs;
  VpiObject lo;
  VpiObject hi;

  auto full = VpiCycleDelayOperands(&lhs, &rhs, &lo, &hi);
  ASSERT_EQ(full.size(), 4u);
  EXPECT_EQ(full[0], &lhs);
  EXPECT_EQ(full[1], &rhs);
  EXPECT_EQ(full[2], &lo);
  EXPECT_EQ(full[3], &hi);

  auto eq = VpiCycleDelayOperands(&lhs, &rhs, &lo, &lo);
  ASSERT_EQ(eq.size(), 3u);
  EXPECT_EQ(eq[0], &lhs);
  EXPECT_EQ(eq[1], &rhs);
  EXPECT_EQ(eq[2], &lo);

  // No right range supplied -> the two sequences and the left range only.
  auto no_right = VpiCycleDelayOperands(&lhs, &rhs, &lo, nullptr);
  ASSERT_EQ(no_right.size(), 3u);
  EXPECT_EQ(no_right[2], &lo);
}

// Detail 3c (repeat operators [*], [=], [->]): operands are the repeated
// sequence, the left repeat bound, then the right repeat bound; the right bound
// is dropped when equal to the left. The ordering is identical for every repeat
// operator.
TEST(SequenceExprModel, RepeatOperandOrderAndBoundOmission) {
  VpiObject seq;
  VpiObject lo;
  VpiObject hi;

  auto full = VpiRepeatOperands(&seq, &lo, &hi);
  ASSERT_EQ(full.size(), 3u);
  EXPECT_EQ(full[0], &seq);
  EXPECT_EQ(full[1], &lo);
  EXPECT_EQ(full[2], &hi);

  auto single = VpiRepeatOperands(&seq, &lo, &lo);
  ASSERT_EQ(single.size(), 2u);
  EXPECT_EQ(single[0], &seq);
  EXPECT_EQ(single[1], &lo);

  auto no_right = VpiRepeatOperands(&seq, &lo, nullptr);
  ASSERT_EQ(no_right.size(), 2u);
}

// Detail 1: vpiArgument returns actuals in formal-declaration order, and a
// formal that carries a default contributes that default when the instance does
// not provide an actual for it.
TEST(SequenceExprModel, ArgumentsFollowFormalOrderAndFillDefaults) {
  VpiObject a0;
  VpiObject a2;
  VpiObject def1;

  std::vector<VpiSequenceFormal> formals = {
      {nullptr},  // formal 0: no default
      {&def1},    // formal 1: has a default value
      {nullptr},  // formal 2: no default
  };
  std::vector<VpiHandle> provided = {&a0, nullptr, &a2};  // formal 1 omitted

  auto args = VpiSequenceInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 3u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);  // default substituted, keeping declaration order
  EXPECT_EQ(args[2], &a2);
}

// Detail 1 edge: when the instance supplies an actual the formal's default is
// not used, and the result is exactly the supplied actuals in formal order.
TEST(SequenceExprModel, ArgumentsUseSuppliedActualsOverDefaults) {
  VpiObject a0;
  VpiObject a1;
  VpiObject def1;

  std::vector<VpiSequenceFormal> formals = {{nullptr}, {&def1}};
  std::vector<VpiHandle> provided = {&a0, &a1};

  auto args = VpiSequenceInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &a1);  // the supplied actual wins over the default
}

// Detail 1 edge: a formal that is neither supplied nor defaulted leaves an
// empty slot, while the result still lines up one-to-one with the declared
// formals.
TEST(SequenceExprModel, OmittedFormalWithoutDefaultYieldsNoArgument) {
  VpiObject a0;

  std::vector<VpiSequenceFormal> formals = {{nullptr}, {nullptr}};
  std::vector<VpiHandle> provided = {&a0,
                                     nullptr};  // formal 1 omitted, no default

  auto args = VpiSequenceInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], nullptr);
}

// Detail 1 edge: the result follows formal-declaration order, so formals beyond
// the end of the provided actuals still contribute their defaults.
TEST(SequenceExprModel, TrailingFormalsBeyondProvidedUseDefaults) {
  VpiObject a0;
  VpiObject def1;

  std::vector<VpiSequenceFormal> formals = {{nullptr}, {&def1}};
  std::vector<VpiHandle> provided = {&a0};  // shorter than the formal list

  auto args = VpiSequenceInstArguments(formals, provided);
  ASSERT_EQ(args.size(), 2u);
  EXPECT_EQ(args[0], &a0);
  EXPECT_EQ(args[1], &def1);  // trailing formal falls back to its default
}

// D5: an argument of a sequence instance is a named event or a sequence
// expression; other object kinds are not valid arguments.
TEST(SequenceExprModel, SequenceArgumentKindsAreNamedEventOrSequenceExpr) {
  EXPECT_TRUE(VpiIsSequenceArgumentType(vpiNamedEvent));
  EXPECT_TRUE(VpiIsSequenceArgumentType(vpiSequenceInst));
  EXPECT_TRUE(VpiIsSequenceArgumentType(vpiOperation));
  EXPECT_TRUE(VpiIsSequenceArgumentType(vpiConstant));

  EXPECT_FALSE(VpiIsSequenceArgumentType(vpiNet));
  EXPECT_FALSE(VpiIsSequenceArgumentType(vpiModule));
}

// D4: a sequence instance resolves to the sequence declaration it instantiates,
// and reports none when no declaration is attached or the handle is null.
TEST(SequenceExprModel, SequenceInstResolvesItsDeclaration) {
  VpiObject inst;
  inst.type = vpiSequenceInst;
  VpiObject decl;
  decl.type = vpiSequenceDecl;
  inst.children = {&decl};
  EXPECT_EQ(VpiSequenceInstDecl(&inst), &decl);

  VpiObject lone;
  lone.type = vpiSequenceInst;
  EXPECT_EQ(VpiSequenceInstDecl(&lone), nullptr);
  EXPECT_EQ(VpiSequenceInstDecl(nullptr), nullptr);
}

// D4 edge: the relation matches by the declaration kind, so an instance whose
// children are all something other than a sequence declaration resolves to
// none.
TEST(SequenceExprModel, SequenceInstWithOnlyOtherChildrenResolvesNone) {
  VpiObject inst;
  inst.type = vpiSequenceInst;
  VpiObject named_event;
  named_event.type = vpiNamedEvent;
  VpiObject operand;
  operand.type = vpiOperation;
  inst.children = {&named_event, &operand};

  EXPECT_EQ(VpiSequenceInstDecl(&inst), nullptr);
}

// D6: a sequence's bare-expression match items are assignments or task/function
// calls; other object kinds are not match items.
TEST(SequenceExprModel, MatchItemKindsAreAssignmentsAndTfCalls) {
  EXPECT_TRUE(VpiIsMatchItemType(vpiAssignment));
  EXPECT_TRUE(VpiIsMatchItemType(vpiFuncCall));
  EXPECT_TRUE(VpiIsMatchItemType(vpiTaskCall));

  EXPECT_FALSE(VpiIsMatchItemType(vpiNet));
  EXPECT_FALSE(VpiIsMatchItemType(vpiOperation));
}

// D6: iterating vpiMatchItem over a bare expression returns exactly its
// assignment/tf-call children, in order, skipping anything else.
TEST(SequenceExprModel, MatchItemsCollectAssignmentAndTfCallChildren) {
  VpiObject expr;
  VpiObject assign;
  assign.type = vpiAssignment;
  VpiObject call;
  call.type = vpiTaskCall;
  VpiObject other;
  other.type = vpiOperation;
  expr.children = {&assign, &other, &call};

  auto items = VpiExprMatchItems(&expr);
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0], &assign);
  EXPECT_EQ(items[1], &call);

  EXPECT_TRUE(VpiExprMatchItems(nullptr).empty());
}

}  // namespace
}  // namespace delta
