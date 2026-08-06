#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.59 Expressions: the VPI object model for an expression. The expr class
// groups operations, constants, part-selects and indexed part-selects, the
// func/method-func/sys-func calls, let expressions, and a simple expression (a
// reference). Operations report vpiOpType, constants vpiConstType, and indexed
// part-selects vpiIndexedPartSelectType; every expression exposes vpiDecompile,
// vpiSize and a value. The subclause's details fix operand orders for the
// multiplier-style and assignment-pattern operators, the cast representation,
// the typespec-availability guarantee, the vpiDecompile spacing rules, the
// part-select vpiConstantSelect rule, the part-select vpiParent, and the
// guarantee that a protected expression still exposes vpiSize. These tests
// observe the production helpers and Get cases in vpi.cpp that apply those
// rules.

// Diagram: the expr class groups exactly the drawn member kinds; variables,
// nets and other objects are not expressions.
TEST(ExpressionModel, ExprClassGroupsItsMemberKinds) {
  for (int type : {vpiOperation, vpiConstant, vpiPartSelect,
                   vpiIndexedPartSelect, vpiFuncCall, vpiMethodFuncCall,
                   vpiSysFuncCall, vpiLetExpr, vpiRefObj}) {
    EXPECT_TRUE(VpiIsExprType(type)) << "type=" << type;
  }

  EXPECT_FALSE(VpiIsExprType(vpiReg));
  EXPECT_FALSE(VpiIsExprType(vpiNet));
  EXPECT_FALSE(VpiIsExprType(vpiModule));
}

// Detail 1: a vpiMultiConcatOp operation reports the multiplier first, then the
// expressions within the concatenation, in order.
TEST(ExpressionModel, MultiConcatOperandOrder) {
  VpiObject mult;
  VpiObject a;
  VpiObject b;

  auto operands = VpiMultiConcatOperands(&mult, {&a, &b});
  ASSERT_EQ(operands.size(), 3u);
  EXPECT_EQ(operands[0], &mult);
  EXPECT_EQ(operands[1], &a);
  EXPECT_EQ(operands[2], &b);

  // The multiplier alone is still the first operand when nothing is
  // concatenated.
  auto just_mult = VpiMultiConcatOperands(&mult, {});
  ASSERT_EQ(just_mult.size(), 1u);
  EXPECT_EQ(just_mult[0], &mult);
}

// Detail 7: a vpiMultiAssignmentPatternOp operation reports the multiplier
// first, then the expressions within the assignment pattern - the same shape as
// multiconcat but for a distinct operator.
TEST(ExpressionModel, MultiAssignmentPatternOperandOrder) {
  VpiObject mult;
  VpiObject y;

  // '{2{y}} -> multiplier 2, then y.
  auto operands = VpiMultiAssignmentPatternOperands(&mult, {&y});
  ASSERT_EQ(operands.size(), 2u);
  EXPECT_EQ(operands[0], &mult);
  EXPECT_EQ(operands[1], &y);
}

// Detail 7 (edge): with no pattern expressions the multiplier is still the one
// and only first operand, mirroring the multiconcat empty case for the distinct
// operator.
TEST(ExpressionModel, MultiAssignmentPatternMultiplierAloneWhenPatternEmpty) {
  VpiObject mult;

  auto operands = VpiMultiAssignmentPatternOperands(&mult, {});
  ASSERT_EQ(operands.size(), 1u);
  EXPECT_EQ(operands[0], &mult);
}

// Detail 3: a cast operation is unary; its only operand is the expression being
// cast (its target type is the typespec, not an operand).
TEST(ExpressionModel, CastOpIsUnary) {
  VpiObject cast_arg;

  auto operands = VpiCastOpOperands(&cast_arg);
  ASSERT_EQ(operands.size(), 1u);
  EXPECT_EQ(operands[0], &cast_arg);
}

// Detail 6: an assignment pattern's keyed entries resolve to positional
// notation; positions not given a value take the default key's value, and the
// result lists the positions in order.
TEST(ExpressionModel, AssignmentPatternResolvesToPositional) {
  VpiObject member0;
  VpiObject member1;
  VpiObject def;

  // '{0: member0, 2: member1, default: def} over four positions ->
  // member0, def, member1, def.
  std::vector<VpiAssignmentPatternEntry> positioned = {{0, &member0},
                                                       {2, &member1}};
  auto operands = VpiAssignmentPatternPositionalOperands(4, positioned, &def);
  ASSERT_EQ(operands.size(), 4u);
  EXPECT_EQ(operands[0], &member0);
  EXPECT_EQ(operands[1], &def);
  EXPECT_EQ(operands[2], &member1);
  EXPECT_EQ(operands[3], &def);
}

// Detail 6 (nesting): a value that is itself an assignment-pattern operation is
// kept as a single nested handle, so nesting is preserved rather than
// flattened.
TEST(ExpressionModel, AssignmentPatternPreservesNesting) {
  VpiObject nested;
  nested.type = vpiOperation;
  nested.op_type = vpiAssignmentPatternOp;
  VpiObject def;

  auto operands =
      VpiAssignmentPatternPositionalOperands(2, {{0, &nested}}, &def);
  ASSERT_EQ(operands.size(), 2u);
  EXPECT_EQ(operands[0], &nested);  // the nested pattern stays one handle
  EXPECT_EQ(operands[0]->op_type, vpiAssignmentPatternOp);
  EXPECT_EQ(operands[1], &def);
}

// Detail 6 (edge/error): an entry whose target position lies outside the
// pattern's position range (too large, or negative) is ignored rather than
// overrunning the operand list, and a pattern with no positions at all is
// empty. The remaining positions still take the default value.
TEST(ExpressionModel, AssignmentPatternIgnoresOutOfRangePositions) {
  VpiObject good;
  VpiObject stray_high;
  VpiObject stray_neg;
  VpiObject def;

  // Position 0 is in range; positions 5 and -1 are out of range for two slots
  // and must be dropped, leaving slot 1 at the default.
  std::vector<VpiAssignmentPatternEntry> entries = {
      {0, &good}, {5, &stray_high}, {-1, &stray_neg}};
  auto operands = VpiAssignmentPatternPositionalOperands(2, entries, &def);
  ASSERT_EQ(operands.size(), 2u);
  EXPECT_EQ(operands[0], &good);
  EXPECT_EQ(operands[1], &def);

  // Zero slots yields no operands regardless of the entries supplied.
  auto none = VpiAssignmentPatternPositionalOperands(0, {{0, &good}}, &def);
  EXPECT_TRUE(none.empty());
}

// Detail 5: the one-to-one typespec relation is always available for a cast
// operation, for a simple expression, and for an assignment-pattern operation
// only when its braces are prefixed by a data type name.
TEST(ExpressionModel, TypespecAvailabilityGuarantee) {
  // Simple expression: always available regardless of op type.
  EXPECT_TRUE(VpiTypespecAlwaysAvailable(0, /*is_simple_expr=*/true, false));

  // Cast operation: always available.
  EXPECT_TRUE(VpiTypespecAlwaysAvailable(vpiCastOp, false, false));

  // Assignment-pattern operations: only when the braces carry a data type
  // prefix.
  EXPECT_TRUE(
      VpiTypespecAlwaysAvailable(vpiAssignmentPatternOp, false,
                                 /*assignment_pattern_has_type_prefix=*/true));
  EXPECT_TRUE(
      VpiTypespecAlwaysAvailable(vpiMultiAssignmentPatternOp, false,
                                 /*assignment_pattern_has_type_prefix=*/true));
  EXPECT_FALSE(
      VpiTypespecAlwaysAvailable(vpiAssignmentPatternOp, false,
                                 /*assignment_pattern_has_type_prefix=*/false));

  // Any other expression: implementation dependent, so not guaranteed.
  EXPECT_FALSE(VpiTypespecAlwaysAvailable(vpiAddOp, false, false));
}

// Detail 5 (negative, second admitted operator): the type-prefix requirement
// applies equally to a multiassignment-pattern operation. Without a data type
// prefix on its braces the typespec relation is not guaranteed, mirroring the
// plain assignment-pattern negative case for the distinct operator.
TEST(ExpressionModel,
     MultiAssignmentPatternTypespecNotGuaranteedWithoutPrefix) {
  EXPECT_FALSE(
      VpiTypespecAlwaysAvailable(vpiMultiAssignmentPatternOp, false,
                                 /*assignment_pattern_has_type_prefix=*/false));
}

// Detail 9: vpiConstantSelect of a part-select or indexed part-select is TRUE
// only when all three conditions hold, and FALSE if any one fails.
TEST(ExpressionModel, PartSelectConstantSelectRequiresAllThreeConditions) {
  VpiPartSelectConstantSelectQuery all_true;
  all_true.parent_constant_select = true;
  all_true.parent_array_has_static_bounds = true;
  all_true.all_range_exprs_constant = true;
  EXPECT_TRUE(VpiPartSelectConstantSelect(all_true));

  // Drop the parent's own constant-select -> FALSE.
  VpiPartSelectConstantSelectQuery q1 = all_true;
  q1.parent_constant_select = false;
  EXPECT_FALSE(VpiPartSelectConstantSelect(q1));

  // Parent is not an array with static bounds -> FALSE.
  VpiPartSelectConstantSelectQuery q2 = all_true;
  q2.parent_array_has_static_bounds = false;
  EXPECT_FALSE(VpiPartSelectConstantSelect(q2));

  // A range expression is not an elaboration-time constant -> FALSE.
  VpiPartSelectConstantSelectQuery q3 = all_true;
  q3.all_range_exprs_constant = false;
  EXPECT_FALSE(VpiPartSelectConstantSelect(q3));
}

// Detail 10: the vpiParent of a part-select or indexed part-select is the
// expression with the trailing (part-)select removed, matching every row of
// Table 37-1 for the declaration logic [0:3][7:0] r [1:4].
TEST(ExpressionModel, PartSelectParentRemovesTrailingSelect) {
  EXPECT_EQ(VpiPartSelectParentExpr("r[4][3][1:0]"), "r[4][3]");
  EXPECT_EQ(VpiPartSelectParentExpr("r[i+1][3][j+:2]"), "r[i+1][3]");
  EXPECT_EQ(VpiPartSelectParentExpr("r[0][j-:4]"), "r[0]");
  EXPECT_EQ(VpiPartSelectParentExpr("r[0:2]"), "r");
}

// Detail 10 (edge): an expression without a trailing bracketed selection has
// nothing to remove and trailing white space does not change the result.
TEST(ExpressionModel, PartSelectParentEdgeCases) {
  EXPECT_EQ(VpiPartSelectParentExpr("r"), "r");
  EXPECT_EQ(VpiPartSelectParentExpr("r[0:2]  "), "r");
}

// Detail 2: vpiDecompile separates each operand and operator with a single
// space, and adds no double or boundary spaces for empty pieces.
TEST(ExpressionModel, DecompileJoinUsesSingleSpaces) {
  EXPECT_EQ(VpiDecompileJoin({"a", "+", "b"}), "a + b");

  // Empty pieces are dropped so the single-space rule is never violated.
  EXPECT_EQ(VpiDecompileJoin({"a", "", "+", "", "b"}), "a + b");
  EXPECT_EQ(VpiDecompileJoin({"x"}), "x");
}

// Detail 2: parentheses preserve precedence and introduce no white space - none
// inside the parentheses and none around them.
TEST(ExpressionModel, DecompileParenthesizeAddsNoWhitespace) {
  EXPECT_EQ(VpiDecompileParenthesize("a + b"), "(a + b)");

  // Composed with the join, a parenthesized operand still has single spacing
  // and no padding next to the parentheses.
  std::string inner =
      VpiDecompileParenthesize(VpiDecompileJoin({"a", "+", "b"}));
  EXPECT_EQ(VpiDecompileJoin({inner, "*", "c"}), "(a + b) * c");
}

// Detail 4 / diagram: a constant reports its constant type through
// vpi_get(vpiConstType); vpiUnboundedConst names the $ used in assertion
// ranges.
TEST(ExpressionModel, ConstantReportsConstType) {
  VpiContext ctx;
  VpiObject c;
  c.type = vpiConstant;
  c.const_type = vpiUnboundedConst;
  EXPECT_EQ(ctx.Get(vpiConstType, &c), vpiUnboundedConst);

  // An unset constant reports zero rather than garbage.
  VpiObject unset;
  unset.type = vpiConstant;
  EXPECT_EQ(ctx.Get(vpiConstType, &unset), 0);
}

// Diagram: an indexed part-select reports its index-part-select type through
// vpi_get(vpiIndexedPartSelectType).
TEST(ExpressionModel, IndexedPartSelectReportsItsType) {
  VpiContext ctx;
  VpiObject ips;
  ips.type = vpiIndexedPartSelect;
  ips.indexed_part_select_type = vpiPosIndexed;  // the +: ascending selection
  EXPECT_EQ(ctx.Get(vpiIndexedPartSelectType, &ips), vpiPosIndexed);
}

// Diagram (edge): the descending +/- direction round-trips through the same Get
// case, and an indexed part-select with no recorded direction reports zero
// rather than garbage.
TEST(ExpressionModel, IndexedPartSelectReportsNegativeAndUnsetType) {
  VpiContext ctx;

  VpiObject down;
  down.type = vpiIndexedPartSelect;
  down.indexed_part_select_type = vpiNegIndexed;  // the -: descending selection
  EXPECT_EQ(ctx.Get(vpiIndexedPartSelectType, &down), vpiNegIndexed);

  VpiObject unset;
  unset.type = vpiIndexedPartSelect;
  EXPECT_EQ(ctx.Get(vpiIndexedPartSelectType, &unset), 0);
}

// Detail 8: a protected expression still permits access to vpiSize - the
// property passes through the protected-object guard and records no error.
TEST(ExpressionModel, ProtectedExpressionPermitsVpiSize) {
  VpiContext ctx;
  VpiObject op;
  op.type = vpiOperation;
  op.size = 8;
  op.is_protected = true;

  EXPECT_EQ(ctx.Get(vpiSize, &op), 8);
  EXPECT_EQ(ctx.LastError().level, 0);  // no error recorded
}

// Detail 8 (scope): the carve-out is for expressions and the vpiSize property
// only. A protected expression queried for some other property is still an
// error, confirming the carve-out does not reopen the whole object.
TEST(ExpressionModel, ProtectedExpressionStillGuardsOtherProperties) {
  VpiContext ctx;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiAddOp;
  op.is_protected = true;

  EXPECT_EQ(ctx.Get(vpiOpType, &op), vpiUndefined);
  EXPECT_NE(ctx.LastError().level, 0);
}

// Detail 8 (scope): the carve-out is keyed on the object being an expression. A
// protected non-expression (a variable) still has vpiSize guarded, so the
// carve- out does not leak to other object kinds.
TEST(ExpressionModel, ProtectedNonExpressionStillGuardsVpiSize) {
  VpiContext ctx;
  VpiObject reg;
  reg.type = vpiReg;
  reg.size = 16;
  reg.is_protected = true;

  EXPECT_EQ(ctx.Get(vpiSize, &reg), vpiUndefined);
  EXPECT_NE(ctx.LastError().level, 0);
}

}  // namespace
}  // namespace delta
