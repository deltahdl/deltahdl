#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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
//
// One of the members drawn inside it is the `simple expr` class, and §37.4.1
// makes a class a grouping of other objects and classes rather than a kind of
// its own, so what the expr class holds includes what that one holds. §37.58
// draws `simple expr` holding a ref obj, a parameter, a spec param, a var
// select and a bit select. Only the ref obj was admitted here, as though a
// reference were the whole of a simple expression, so an expression written as
// any of the other four was an expression to nothing.
TEST(ExpressionModel, ExprClassGroupsItsMemberKinds) {
  for (int type : {vpiOperation, vpiConstant, vpiPartSelect,
                   vpiIndexedPartSelect, vpiFuncCall, vpiMethodFuncCall,
                   vpiSysFuncCall, vpiLetExpr, vpiRefObj}) {
    EXPECT_TRUE(VpiIsExprType(type)) << "type=" << type;
  }

  // §37.58: the rest of what the nested `simple expr` class groups.
  for (int type : {vpiParameter, vpiSpecParam, vpiVarSelect, vpiBitSelect}) {
    EXPECT_TRUE(VpiIsExprType(type)) << "simple expr type=" << type;
  }

  // The nets and variables classes drawn beside those five stay out: §37.3.5
  // detail 8 carves out only a protected expression, so a protected variable
  // keeps its properties guarded.
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

// A design whose one continuous assignment's right side is the expression a
// case is about, run with a PLI application registered.
class ExpressionsOfARun : public VpiDesignRun {
 protected:
  // The right side of the top's continuous assignment.
  static vpiHandle Rhs() {
    vpiHandle it =
        vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }

  // The integer value of an expression object.
  static int IntOf(vpiHandle expr) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(expr, &value);
    return value.value.integer;
  }

  // The operands of an operation, in order.
  static std::vector<vpiHandle> OperandsOf(vpiHandle op) {
    std::vector<vpiHandle> operands;
    vpiHandle it = vpi_iterate(vpiOperand, op);
    if (it == nullptr) return operands;
    while (vpiHandle operand = vpi_scan(it)) operands.push_back(operand);
    return operands;
  }
};

constexpr const char* kPartSelect =
    "module top; wire [7:0] a; wire [3:0] y; assign y = a[7:4]; endmodule\n";

// §37.59: a part select is an expression of its own...
TEST_F(ExpressionsOfARun, APartSelectIsAPartSelectObject) {
  Run(kPartSelect);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiPartSelect);
}

// ...whose parent is the object it selects into...
TEST_F(ExpressionsOfARun, APartSelectsParentIsWhatItSelectsInto) {
  Run(kPartSelect);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Rhs())), "a");
}

// ...and whose range is the two bounds the source wrote.
TEST_F(ExpressionsOfARun, APartSelectsLeftRangeIsItsFirstBound) {
  Run(kPartSelect);
  EXPECT_EQ(IntOf(vpi_handle(vpiLeftRange, Rhs())), 7);
}

TEST_F(ExpressionsOfARun, APartSelectsRightRangeIsItsSecondBound) {
  Run(kPartSelect);
  EXPECT_EQ(IntOf(vpi_handle(vpiRightRange, Rhs())), 4);
}

constexpr const char* kIndexedPartSelect =
    "module top; wire [7:0] a; wire [3:0] y; assign y = a[2 +: 4]; "
    "endmodule\n";

// §37.59: an indexed part select is an expression of its own, ascending for
// +:, with the base and width the source wrote.
TEST_F(ExpressionsOfARun, AnIndexedPartSelectIsAnIndexedPartSelectObject) {
  Run(kIndexedPartSelect);
  EXPECT_EQ(vpi_get(vpiType, Rhs()), vpiIndexedPartSelect);
}

TEST_F(ExpressionsOfARun, AnAscendingIndexedPartSelectIsPosIndexed) {
  Run(kIndexedPartSelect);
  EXPECT_EQ(vpi_get(vpiIndexedPartSelectType, Rhs()), vpiPosIndexed);
}

TEST_F(ExpressionsOfARun, ADescendingIndexedPartSelectIsNegIndexed) {
  Run("module top; wire [7:0] a; wire [3:0] y; assign y = a[5 -: 4]; "
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiIndexedPartSelectType, Rhs()), vpiNegIndexed);
}

TEST_F(ExpressionsOfARun, AnIndexedPartSelectsBaseIsItsStart) {
  Run(kIndexedPartSelect);
  EXPECT_EQ(IntOf(vpi_handle(vpiBaseExpr, Rhs())), 2);
}

TEST_F(ExpressionsOfARun, AnIndexedPartSelectsWidthIsItsWidth) {
  Run(kIndexedPartSelect);
  EXPECT_EQ(IntOf(vpi_handle(vpiWidthExpr, Rhs())), 4);
}

TEST_F(ExpressionsOfARun, AnIndexedPartSelectsParentIsWhatItSelectsInto) {
  Run(kIndexedPartSelect);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiParent, Rhs())), "a");
}

constexpr const char* kReplication =
    "module top; wire a; wire [1:0] y; assign y = {2{a}}; endmodule\n";

// §37.59: a replication is a multiple concatenation operation...
TEST_F(ExpressionsOfARun, AReplicationIsAMultiConcatOperation) {
  Run(kReplication);
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiMultiConcatOp);
}

// ...whose first operand is the multiplier (detail 1)...
TEST_F(ExpressionsOfARun, AReplicationsFirstOperandIsTheMultiplier) {
  Run(kReplication);
  std::vector<vpiHandle> operands = OperandsOf(Rhs());
  ASSERT_EQ(operands.size(), 2U);
  EXPECT_EQ(IntOf(operands[0]), 2);
}

// ...and whose remaining operands are the concatenated expressions.
TEST_F(ExpressionsOfARun, AReplicationsLaterOperandsAreTheElements) {
  Run(kReplication);
  std::vector<vpiHandle> operands = OperandsOf(Rhs());
  ASSERT_EQ(operands.size(), 2U);
  EXPECT_STREQ(vpi_get_str(vpiName, operands[1]), "a");
}

// §37.59: a cast, an inside expression, a streaming concatenation in either
// direction, a min:typ:max and an implication are operations of their own.
TEST_F(ExpressionsOfARun, ACastIsACastOperation) {
  Run("module top; wire [7:0] a; wire [31:0] y; assign y = int'(a); "
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiCastOp);
}

TEST_F(ExpressionsOfARun, AnInsideExpressionIsAnInsideOperation) {
  Run("module top; wire [7:0] a; wire y; assign y = a inside {1, 2}; "
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiInsideOp);
}

TEST_F(ExpressionsOfARun, ARightToLeftStreamIsAStreamRLOperation) {
  Run("module top; wire [7:0] a, y; assign y = {<<{a}}; endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiStreamRLOp);
}

TEST_F(ExpressionsOfARun, ALeftToRightStreamIsAStreamLROperation) {
  Run("module top; wire [7:0] a, y; assign y = {>>{a}}; endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiStreamLROp);
}

TEST_F(ExpressionsOfARun, AMinTypMaxIsAMinTypMaxOperation) {
  Run("module top; wire a, b, c, y; assign y = (a:b:c); endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiMinTypMaxOp);
}

TEST_F(ExpressionsOfARun, AnImplicationIsAnImplyOperation) {
  Run("module top; wire a, b, y; assign y = (a -> b); endmodule\n");
  EXPECT_EQ(vpi_get(vpiOpType, Rhs()), vpiImplyOp);
}

// Detail 2: an expression of a run decompiles to an equivalent one, each
// operand and operator one space apart however the source spaced them...
TEST_F(ExpressionsOfARun, AnOperationDecompilesOneSpaceApart) {
  Run("module top; wire [7:0] a, b, y; assign y = a+b; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a + b");
}

// ...parenthesized where precedence needs it and nowhere else, without white
// space of their own...
TEST_F(ExpressionsOfARun, ParenthesesStandWherePrecedenceNeedsThem) {
  Run("module top; wire [7:0] a, b, c, y; assign y = (a + b) * c; "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "(a + b) * c");
}

TEST_F(ExpressionsOfARun, ParenthesesPrecedenceDoesNotNeedAreDropped) {
  Run("module top; wire [7:0] a, b, c, y; assign y = a + (b * c); "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a + b * c");
}

// ...including those keeping a right operand of a left associative operator
// whole...
TEST_F(ExpressionsOfARun, ARightOperandOfALeftAssociativeOperatorStaysWhole) {
  Run("module top; wire [7:0] a, b, c, y; assign y = a - (b - c); "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a - (b - c)");
}

// ...a unary operator one space from its operand...
TEST_F(ExpressionsOfARun, AUnaryOperatorStandsOneSpaceFromItsOperand) {
  Run("module top; wire [7:0] a, b, y; assign y = ~(a & b) + -a; "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "~ (a & b) + - a");
}

// ...a conditional whose condition is itself one in parentheses...
TEST_F(ExpressionsOfARun, AConditionalDecompilesWithItsOperators) {
  Run("module top; wire s, t; wire [7:0] a, b, y;\n"
      "  assign y = (s?t:s) ? a+1 : b; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "(s ? t : s) ? a + 1 : b");
}

// ...a constant as the literal written...
TEST_F(ExpressionsOfARun, AConstantDecompilesToItsLiteral) {
  Run("module top; wire [7:0] y; assign y = 8'hA5; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "8'hA5");
}

// ...a select with what it selects into...
TEST_F(ExpressionsOfARun, ASelectDecompilesAfterItsBase) {
  Run(kPartSelect);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a[7:4]");
}

TEST_F(ExpressionsOfARun, AnIndexedPartSelectDecompilesAfterItsBase) {
  Run(kIndexedPartSelect);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a[2+:4]");
}

// ...a concatenation and a replication with their elements...
TEST_F(ExpressionsOfARun, AConcatenationDecompilesWithItsElements) {
  Run("module top; wire [3:0] a, b; wire [7:0] y; assign y = {a,b}; "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "{a, b}");
}

TEST_F(ExpressionsOfARun, AReplicationDecompilesWithItsMultiplier) {
  Run(kReplication);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "{2{a}}");
}

// ...a call with its arguments...
TEST_F(ExpressionsOfARun, ACallDecompilesWithItsArguments) {
  Run("module top;\n"
      "  function automatic int f(int x, int z); return x; endfunction\n"
      "  wire [31:0] a, y; assign y = f(a+1,a); endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "f(a + 1, a)");
}

// ...an array method call with its with clause (#5038)...
TEST_F(ExpressionsOfARun, AWithClauseDecompilesAfterItsCall) {
  Run("module top; int arr[3]; wire [31:0] y;\n"
      "  assign y = arr.sum() with (item*2); endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "arr.sum() with (item * 2)");
}

// ...a randomize() call with its inline constraint block (§18.7, #5039)...
TEST_F(ExpressionsOfARun, AnInlineConstraintBlockDecompilesAfterItsCall) {
  Run("module top; int a; wire [31:0] y;\n"
      "  assign y = std::randomize(a) with {a>0; soft a<9;}; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()),
               "std::randomize(a) with {a > 0; soft a < 9;}");
}

// ...with the identifier list that restricts it...
TEST_F(ExpressionsOfARun, ARestrictedBlockDecompilesWithItsIdentifierList) {
  Run("module top; class C; rand int x; endclass C c = new;\n"
      "  wire [31:0] y; assign y = c.randomize() with (x) {x>0;};\n"
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()),
               "c.randomize() with (x) {x > 0;}");
}

// ...each constraint set an item governs in braces...
TEST_F(ExpressionsOfARun, AGoverningItemDecompilesWithItsSets) {
  Run("module top; int a, b; wire [31:0] y;\n"
      "  assign y = std::randomize(a, b) with {solve b before a;\n"
      "    b -> a!=0; if (b>1) a<4; else a>8;}; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()),
               "std::randomize(a, b) with {solve b before a; b -> {a != 0;} "
               "if (b > 1) {a < 4;} else {a > 8;}}");
}

// ...and each distribution, uniqueness, iteration and disabling as written...
TEST_F(ExpressionsOfARun, AConstraintItemDecompilesAsWritten) {
  Run("module top; int a, b; int q[4]; wire [31:0] y;\n"
      "  assign y = std::randomize(a, b) with {a dist {0:=1, [1:3]:/2};\n"
      "    unique {a, b}; foreach (q[i]) q[i]<a; disable soft a;};\n"
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()),
               "std::randomize(a, b) with {a dist {0 := 1, [1:3] :/ 2}; "
               "unique {a, b}; foreach (q[i]) {q[i] < a;} disable soft a;}");
}

// ...a cast with the type it casts to...
TEST_F(ExpressionsOfARun, ACastDecompilesWithItsType) {
  Run("module top; wire [7:0] a; wire [31:0] y; assign y = int'(a+1); "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "int'(a + 1)");
}

// ...an inside expression with its set, ranges among it...
TEST_F(ExpressionsOfARun, AnInsideExpressionDecompilesWithItsSet) {
  Run("module top; wire [7:0] a; wire y; assign y = a inside {1,[2:3]}; "
      "endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "a inside {1, [2:3]}");
}

// ...a streaming concatenation with its direction...
TEST_F(ExpressionsOfARun, AStreamDecompilesWithItsDirection) {
  Run("module top; wire [7:0] a, y; assign y = {<<{a}}; endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "{<< {a}}");
}

// ...a min:typ:max in its parentheses...
TEST_F(ExpressionsOfARun, AMinTypMaxDecompilesInItsParentheses) {
  Run("module top; wire a, b, c, y; assign y = (a:b:c); endmodule\n");
  EXPECT_STREQ(vpi_get_str(vpiDecompile, Rhs()), "(a : b : c)");
}

// ...and each operand of an operation decompiles on its own.
TEST_F(ExpressionsOfARun, AnOperandDecompilesOnItsOwn) {
  Run("module top; wire [7:0] a, b, c, y; assign y = (a + b) * c; "
      "endmodule\n");
  std::vector<vpiHandle> operands = OperandsOf(Rhs());
  ASSERT_EQ(operands.size(), 2U);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, operands[0]), "a + b");
}

// The vpiType of each argument of the call of `$probe` its calltf was last
// run for, in order.
std::vector<int>& ProbedArgumentKinds() {
  static std::vector<int> kinds;
  return kinds;
}

class ArgumentsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    ProbedArgumentKinds().clear();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$probe");
    data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
      vpiHandle it =
          vpi_iterate(vpiArgument, vpi_handle(vpiSysTfCall, nullptr));
      for (vpiHandle h = it != nullptr ? vpi_scan(it) : nullptr; h != nullptr;
           h = vpi_scan(it)) {
        ProbedArgumentKinds().push_back(vpi_get(vpiType, h));
      }
      return 0;
    };
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

// §37.42 with §37.59: an argument a user system task's call carries while
// its calltf runs is the kind of expr its actual is, a call of a function a
// func call, of a system function a sys func call and a literal a constant,
// an operator's expression alone an operation (#5111).
TEST_F(ArgumentsOfARun, ARunTimeArgumentIsTheKindOfExprItsActualIs) {
  Run("module top; int x;\n"
      "  function int inc(); return 1; endfunction\n"
      "  initial $probe(inc(), 5, x + 1, $time);\n"
      "endmodule\n");
  EXPECT_EQ(ProbedArgumentKinds(),
            (std::vector<int>{vpiFuncCall, vpiConstant, vpiOperation,
                              vpiSysFuncCall}));
}

// §37.59 and §37.52: no object and an object that is no operation have no
// operands; an operation's operands include a property expr and leave out a
// child that is no expression.
TEST(ExpressionModel, OperandsAreTheOperationsExpressionChildren) {
  EXPECT_TRUE(VpiOperationOperands(nullptr).empty());
  VpiObject constant;
  constant.type = vpiConstant;
  EXPECT_TRUE(VpiOperationOperands(&constant).empty());
  VpiObject inst;
  inst.type = vpiPropertyInst;
  VpiObject attribute;
  attribute.type = vpiAttribute;
  VpiObject operation;
  operation.type = vpiOperation;
  operation.children = {&inst, &attribute};
  EXPECT_EQ(VpiOperationOperands(&operation), (std::vector<VpiHandle>{&inst}));
}

constexpr const char* kPairPrefix =
    "module top; typedef struct packed { logic a, b; } pair_t;\n"
    "  typedef struct packed { logic [1:0] a; } one_t;\n"
    "  logic x, y; logic [1:0] z; pair_t w; one_t v;\n";

// Detail 6: a positional assignment pattern is an assignment pattern
// operation over its expressions in the order written, one of one expression
// as much as one of two (#5752).
TEST_F(ExpressionsOfARun, APositionalPatternIsAnAssignmentPatternOperation) {
  Run(std::string(kPairPrefix) + "  assign w = '{x, y}; endmodule\n");
  vpiHandle pattern = Rhs();
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[0]), "x");
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[1]), "y");
}

TEST_F(ExpressionsOfARun, AOneExpressionPatternIsAnAssignmentPatternOperation) {
  Run(std::string(kPairPrefix) + "  assign v = '{z}; endmodule\n");
  vpiHandle pattern = Rhs();
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 1U);
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[0]), "z");
}

// Detail 7: a replicated pattern is a multi assignment pattern operation whose
// first operand is the multiplier and whose others are its expressions
// (#5752).
TEST_F(ExpressionsOfARun,
       AReplicatedPatternIsAMultiAssignmentPatternOperation) {
  Run(std::string(kPairPrefix) + "  assign w = '{2 {y}}; endmodule\n");
  vpiHandle pattern = Rhs();
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiMultiAssignmentPatternOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(pattern);
  ASSERT_EQ(kOperands.size(), 2U);
  EXPECT_EQ(IntOf(kOperands[0]), 2);
  EXPECT_STREQ(vpi_get_str(vpiName, kOperands[1]), "y");
}

// A replication written as a pattern's one expression, on the pattern's line
// or on the next, is that expression, a multi concat, and the pattern an
// assignment pattern operation over it (#5752).
void ExpectReplicationIsTheExpression(vpiHandle pattern) {
  ASSERT_NE(pattern, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, pattern), vpiAssignmentPatternOp);
  vpiHandle it = vpi_iterate(vpiOperand, pattern);
  ASSERT_NE(it, nullptr);
  vpiHandle operand = vpi_scan(it);
  ASSERT_NE(operand, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, operand), vpiMultiConcatOp);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(ExpressionsOfARun, AReplicationOnAPatternsLineIsItsExpression) {
  Run(std::string(kPairPrefix) + "  assign v = '{ {2{y}} }; endmodule\n");
  ExpectReplicationIsTheExpression(Rhs());
}

TEST_F(ExpressionsOfARun, AReplicationBelowAPatternIsItsExpression) {
  Run(std::string(kPairPrefix) + "  assign v = '{\n {2{y}} }; endmodule\n");
  ExpectReplicationIsTheExpression(Rhs());
}

// §37.59 detail 10: blank text has no parent expression, and an unbalanced
// trailing selection takes everything with it; a selection with an index
// leaves the name it selects from, an index holding a selection of its own
// among it.
TEST(ExpressionModel, PartSelectParentOfBlankUnbalancedAndIndexedText) {
  EXPECT_EQ(VpiPartSelectParentExpr("  "), "");
  EXPECT_EQ(VpiPartSelectParentExpr("a]"), "");
  EXPECT_EQ(VpiPartSelectParentExpr("a[1]"), "a");
  EXPECT_EQ(VpiPartSelectParentExpr("a[b[1]]"), "a");
}

}  // namespace
}  // namespace delta
