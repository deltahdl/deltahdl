#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.52 property specification: the VPI object model for a property
// specification and the property-expr class. A property spec traverses to a
// clocking event, a disable condition and a property expression; the property
// expr class groups operations, clocked properties, case properties and others;
// an operation's vpiOpType is drawn from a fixed set of property operators with
// defined operand orders and a strength flag; and a case property item groups
// the case conditions that branch to the same property statement. The
// property-expr classification is reused by §37.51's property-declaration
// model, weaving the two subclauses together. These tests observe the
// production helpers in vpi.cpp and the VpiContext methods that apply those
// rules.

// Diagram: the property-expr class groups the member kinds the diagram draws -
// an operation, a multiclock sequence expression, a property instance, a
// clocked property and a case property. Unrelated kinds are not members.
TEST(PropertySpecModel, PropertyExprClassGroupsItsMemberKinds) {
  EXPECT_TRUE(VpiIsPropertyExprType(vpiOperation));
  EXPECT_TRUE(VpiIsPropertyExprType(vpiMulticlockSequenceExpr));
  EXPECT_TRUE(VpiIsPropertyExprType(vpiPropertyInst));
  EXPECT_TRUE(VpiIsPropertyExprType(vpiClockedProperty));
  EXPECT_TRUE(VpiIsPropertyExprType(vpiCaseProperty));

  EXPECT_FALSE(VpiIsPropertyExprType(vpiNet));
  EXPECT_FALSE(VpiIsPropertyExprType(vpiModule));
}

// Diagram edge: the property-expr class selector names the class, not a
// concrete member kind, so it is not itself classified as a member.
TEST(PropertySpecModel, PropertyExprClassSelectorIsNotItselfAMemberKind) {
  EXPECT_FALSE(VpiIsPropertyExprType(vpiPropertyExpr));
}

// Detail 1: property variables are declarations whose value cannot be accessed
// through VPI.
TEST(PropertySpecModel, PropertyVariableValueCannotBeAccessed) {
  EXPECT_FALSE(VpiIsPropertyVariableValueAccessible());
}

// Detail 2: within a property expr vpiOpType is one of exactly the twenty
// listed property operators.
TEST(PropertySpecModel, OpTypeSetCoversTheTwentyPropertyOperators) {
  for (int op : {vpiAcceptOnOp,
                 vpiAlwaysOp,
                 vpiCompAndOp,
                 vpiCompOrOp,
                 vpiEventuallyOp,
                 vpiIfElseOp,
                 vpiIfOp,
                 vpiIffOp,
                 vpiImpliesOp,
                 vpiNexttimeOp,
                 vpiNonOverlapFollowedByOp,
                 vpiNonOverlapImplyOp,
                 vpiNotOp,
                 vpiOverlapFollowedByOp,
                 vpiOverlapImplyOp,
                 vpiRejectOnOp,
                 vpiSyncAcceptOnOp,
                 vpiSyncRejectOnOp,
                 vpiUntilOp,
                 vpiUntilWithOp}) {
    EXPECT_TRUE(VpiIsPropertyExprOpType(op)) << "op=" << op;
  }
}

// Detail 2 edge: operators outside the property set (ordinary expression ops
// and sequence-only operators) are rejected.
TEST(PropertySpecModel, OpTypeSetRejectsNonPropertyOperators) {
  EXPECT_FALSE(VpiIsPropertyExprOpType(vpiAddOp));
  EXPECT_FALSE(VpiIsPropertyExprOpType(vpiLogAndOp));
  EXPECT_FALSE(VpiIsPropertyExprOpType(vpiThroughoutOp));
  EXPECT_FALSE(VpiIsPropertyExprOpType(vpiIntersectOp));
}

// Detail 2: an operation reports its operation type through vpi_get(vpiOpType);
// for a property operation that value is one of the property operators.
TEST(PropertySpecModel, OperationReportsItsPropertyOpType) {
  VpiContext ctx;
  VpiObject op;
  op.type = vpiOperation;
  op.op_type = vpiUntilOp;

  EXPECT_EQ(ctx.Get(vpiOpType, &op), vpiUntilOp);
  EXPECT_TRUE(VpiIsPropertyExprOpType(ctx.Get(vpiOpType, &op)));
}

// Detail 2 (vpiNexttimeOp exception): operands are property then constant, and
// the constant is given only when it differs from 1.
TEST(PropertySpecModel, NexttimeOperandOrderAndConstantOmission) {
  VpiObject prop;
  VpiObject k;

  auto with_constant =
      VpiNexttimeOperands(&prop, &k, /*constant_differs_from_one=*/true);
  ASSERT_EQ(with_constant.size(), 2u);
  EXPECT_EQ(with_constant[0], &prop);
  EXPECT_EQ(with_constant[1], &k);

  // A constant equal to 1 is omitted, leaving just the property.
  auto unit_constant =
      VpiNexttimeOperands(&prop, &k, /*constant_differs_from_one=*/false);
  ASSERT_EQ(unit_constant.size(), 1u);
  EXPECT_EQ(unit_constant[0], &prop);

  // No constant supplied at all -> just the property.
  auto no_constant =
      VpiNexttimeOperands(&prop, nullptr, /*constant_differs_from_one=*/true);
  ASSERT_EQ(no_constant.size(), 1u);
  EXPECT_EQ(no_constant[0], &prop);
}

// Detail 2 (vpiAlwaysOp/vpiEventuallyOp exception): operands are property, left
// range, right range; a null bound is omitted.
TEST(PropertySpecModel, AlwaysEventuallyOperandOrderAndRangeOmission) {
  VpiObject prop;
  VpiObject lo;
  VpiObject hi;

  auto ranged = VpiAlwaysEventuallyOperands(&prop, &lo, &hi);
  ASSERT_EQ(ranged.size(), 3u);
  EXPECT_EQ(ranged[0], &prop);
  EXPECT_EQ(ranged[1], &lo);
  EXPECT_EQ(ranged[2], &hi);

  // Unranged operator -> just the property.
  auto unranged = VpiAlwaysEventuallyOperands(&prop, nullptr, nullptr);
  ASSERT_EQ(unranged.size(), 1u);
  EXPECT_EQ(unranged[0], &prop);

  // One-sided range: only the present bound follows the property, and it keeps
  // its position. A present left bound with an absent right bound yields
  // [property, left].
  auto left_only = VpiAlwaysEventuallyOperands(&prop, &lo, nullptr);
  ASSERT_EQ(left_only.size(), 2u);
  EXPECT_EQ(left_only[0], &prop);
  EXPECT_EQ(left_only[1], &lo);

  // A present right bound with an absent left bound yields [property, right] -
  // the right bound occupies the immediately-following slot, since the omitted
  // left bound is not represented by a placeholder.
  auto right_only = VpiAlwaysEventuallyOperands(&prop, nullptr, &hi);
  ASSERT_EQ(right_only.size(), 2u);
  EXPECT_EQ(right_only[0], &prop);
  EXPECT_EQ(right_only[1], &hi);
}

// Detail 3: vpiOpStrong is valid only for nexttime, always, eventually, until
// and until_with; for every other property operator it does not apply.
TEST(PropertySpecModel, OpStrongIsValidOnlyForTheStrongCapableOperators) {
  for (int op : {vpiNexttimeOp, vpiAlwaysOp, vpiEventuallyOp, vpiUntilOp,
                 vpiUntilWithOp}) {
    EXPECT_TRUE(VpiIsOpStrongValidOp(op)) << "op=" << op;
  }

  EXPECT_FALSE(VpiIsOpStrongValidOp(vpiImpliesOp));
  EXPECT_FALSE(VpiIsOpStrongValidOp(vpiNotOp));
  EXPECT_FALSE(VpiIsOpStrongValidOp(vpiAcceptOnOp));
}

// Detail 3: an operation reports its operator strength through
// vpi_get(vpiOpStrong) - TRUE for the strong version, FALSE otherwise.
TEST(PropertySpecModel, OperationReportsOpStrongProperty) {
  VpiContext ctx;
  VpiObject strong;
  strong.type = vpiOperation;
  strong.op_type = vpiUntilOp;
  strong.op_strong = true;
  EXPECT_EQ(ctx.Get(vpiOpStrong, &strong), 1);

  VpiObject weak;
  weak.type = vpiOperation;
  weak.op_type = vpiUntilOp;
  EXPECT_EQ(ctx.Get(vpiOpStrong, &weak), 0);
}

// Detail 4: a case property item groups all case conditions that branch to the
// same property statement; the property-expr branch is not one of the
// conditions.
TEST(PropertySpecModel, CaseItemGroupsConditionsBranchingToOneStatement) {
  VpiObject item;
  item.type = vpiCasePropertyItem;
  VpiObject c0;
  c0.type = vpiExpr;
  VpiObject c1;
  c1.type = vpiExpr;
  VpiObject branch;
  branch.type = vpiClockedProperty;  // the property statement (a property expr)
  item.children = {&c0, &c1, &branch};

  auto conditions = VpiCaseItemConditions(&item);
  ASSERT_EQ(conditions.size(), 2u);
  EXPECT_EQ(conditions[0], &c0);
  EXPECT_EQ(conditions[1], &c1);

  // The branch is reached as the item's property expression, not as a
  // condition.
  EXPECT_EQ(VpiPropertyExprChild(&item), &branch);
}

// Detail 5: the default case item has no condition expression, so it groups
// none and vpi_iterate() over its conditions returns null.
TEST(PropertySpecModel, DefaultCaseItemHasNoConditionsAndIteratesToNull) {
  VpiContext ctx;
  VpiObject default_item;
  default_item.type = vpiCasePropertyItem;  // default: no condition children

  EXPECT_TRUE(VpiCaseItemConditions(&default_item).empty());
  EXPECT_EQ(ctx.Iterate(vpiExpr, &default_item), nullptr);

  // A non-default item with condition children does iterate to them.
  VpiObject item;
  item.type = vpiCasePropertyItem;
  VpiObject c0;
  c0.type = vpiExpr;
  item.children = {&c0};
  VpiHandle it = ctx.Iterate(vpiExpr, &item);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx.Scan(it), &c0);
  EXPECT_EQ(ctx.Scan(it), nullptr);  // drains and frees the iterator
}

// Diagram (case property -- vpiCondition --> expr): a case property selects on
// a controlling expression reached through vpiCondition. The selecting
// expression is the case property's expression child - distinct from the case
// property items - and the relation resolves through the generic vpi_handle()
// dispatch as well as the dedicated helper. A case property with no condition
// reports none.
TEST(PropertySpecModel, CasePropertySelectsOnItsConditionExpression) {
  VpiContext ctx;
  VpiObject case_prop;
  case_prop.type = vpiCaseProperty;
  VpiObject sel;
  sel.type = vpiExpr;  // the expression the case selects on
  VpiObject item;
  item.type = vpiCasePropertyItem;  // a branch, not the selecting condition
  case_prop.children = {&sel, &item};

  EXPECT_EQ(VpiCasePropertyConditionExpr(&case_prop), &sel);
  // The figure's vpiCondition edge is not served by the generic child walk
  // (no child's type is vpiCondition); the wired relation resolves it.
  EXPECT_EQ(ctx.Handle(vpiCondition, &case_prop), &sel);

  VpiObject no_condition;
  no_condition.type = vpiCaseProperty;
  VpiObject only_item;
  only_item.type = vpiCasePropertyItem;
  no_condition.children = {&only_item};
  EXPECT_EQ(VpiCasePropertyConditionExpr(&no_condition), nullptr);
  EXPECT_EQ(ctx.Handle(vpiCondition, &no_condition), nullptr);
  EXPECT_EQ(VpiCasePropertyConditionExpr(nullptr), nullptr);
}

// Diagram (property spec / clocked property -- vpiClockingEvent --> expr): a
// property spec and a clocked property both traverse to their clocking event,
// reporting none when no clocking event is attached. The relation is shared
// between the two member kinds.
TEST(PropertySpecModel, ClockingEventRelationIsSharedBySpecAndClockedProperty) {
  VpiObject spec;
  spec.type = vpiPropertySpec;
  VpiObject ev;
  ev.type = vpiEventControl;
  spec.children = {&ev};
  EXPECT_EQ(VpiClockingEvent(&spec), &ev);

  VpiObject clocked;
  clocked.type = vpiClockedProperty;
  VpiObject ev2;
  ev2.type = vpiEventControl;
  clocked.children = {&ev2};
  EXPECT_EQ(VpiClockingEvent(&clocked), &ev2);

  VpiObject unclocked;
  unclocked.type = vpiPropertySpec;
  EXPECT_EQ(VpiClockingEvent(&unclocked), nullptr);
  EXPECT_EQ(VpiClockingEvent(nullptr), nullptr);
}

// Diagram (property spec / clocked property -> property expr): the "-> property
// expr" edge reaches the object's property-expr-kind child.
TEST(PropertySpecModel, PropertySpecReachesItsPropertyExpr) {
  VpiObject spec;
  spec.type = vpiPropertySpec;
  VpiObject pe;
  pe.type = vpiOperation;  // a property-expr kind
  spec.children = {&pe};
  EXPECT_EQ(VpiPropertyExprChild(&spec), &pe);

  VpiObject empty;
  empty.type = vpiPropertySpec;
  EXPECT_EQ(VpiPropertyExprChild(&empty), nullptr);
}

// Diagram (clocked property -> property expr): a clocked property reaches its
// property-expr child through the same "-> property expr" edge a property spec
// uses; the relation is shared across the two member kinds. None when no
// property expr is attached.
TEST(PropertySpecModel, ClockedPropertyReachesItsPropertyExpr) {
  VpiObject clocked;
  clocked.type = vpiClockedProperty;
  VpiObject pe;
  pe.type = vpiOperation;  // a property-expr kind
  clocked.children = {&pe};
  EXPECT_EQ(VpiPropertyExprChild(&clocked), &pe);

  VpiObject empty;
  empty.type = vpiClockedProperty;
  EXPECT_EQ(VpiPropertyExprChild(&empty), nullptr);
}

// Diagram (case property -> case property item): a case property iterates to
// its case property items through vpi_iterate(vpiCasePropertyItem, ...), in
// order. Its selecting condition expression (the vpiCondition edge) is not one
// of the items.
TEST(PropertySpecModel, CasePropertyIteratesToItsCasePropertyItems) {
  VpiContext ctx;
  VpiObject case_prop;
  case_prop.type = vpiCaseProperty;
  VpiObject sel;
  sel.type = vpiExpr;  // the selecting condition, not an item
  VpiObject item0;
  item0.type = vpiCasePropertyItem;
  VpiObject item1;
  item1.type = vpiCasePropertyItem;
  case_prop.children = {&sel, &item0, &item1};

  VpiHandle it = ctx.Iterate(vpiCasePropertyItem, &case_prop);
  ASSERT_NE(it, nullptr);
  std::vector<VpiHandle> seen;
  while (VpiHandle h = ctx.Scan(it)) seen.push_back(h);
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &item0);
  EXPECT_EQ(seen[1], &item1);
}

// Diagram (property spec -- vpiDisableCondition --> expr | distribution): a
// property specification's disable condition reaches a bare expression or a
// distribution. The relation is shared with §37.51's property instance, whose
// disable condition reaches only an expression.
TEST(PropertySpecModel, DisableConditionReachesExpressionOrDistribution) {
  EXPECT_TRUE(VpiIsDisableConditionType(vpiExpr));
  EXPECT_TRUE(VpiIsDisableConditionType(vpiDistribution));
  EXPECT_TRUE(VpiIsDisableConditionType(vpiOperation));

  EXPECT_FALSE(VpiIsDisableConditionType(vpiModule));
  EXPECT_FALSE(VpiIsDisableConditionType(vpiNet));
}

}  // namespace
}  // namespace delta
