#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.72 Case, pattern: the object model diagram for the pattern-matching case
// statement. The case object carries the vpiCaseType and vpiQualifier int
// properties; it reaches its condition expression (vpiCondition) and iterates
// its case items. A case item reaches its match expressions through the vpiExpr
// edge (drawn to both the pattern grouping and a plain expr) and branches to
// one statement. Two numbered Details govern the case item: it groups all the
// conditions that branch to one statement (detail 1), and the default case item
// - which has no condition expression - iterates to NULL (detail 2). These
// tests observe the production code that applies those rules: the vpiCaseType
// and vpiQualifier property dispatch (vpi_get), the match-expression grouping
// (VpiCaseItemMatchExprs), and the vpiExpr iteration over a case item
// (Iterate), including the default-item NULL rule.

// The fixture installs a context so the public vpi_get/vpi_iterate entry points
// run their real dispatch over the test objects.
class CasePattern : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Diagram (case object properties): a case statement reports its case kind and
// its qualifier flags as int properties through the public vpi_get dispatch.
TEST_F(CasePattern, CaseStatementReportsCaseTypeAndQualifier) {
  VpiObject case_stmt;
  case_stmt.type = vpiCase;
  case_stmt.case_type = vpiCaseZ;
  case_stmt.qualifier = vpiUniqueQualifier | vpiPriorityQualifier;

  EXPECT_EQ(vpi_get(vpiCaseType, &case_stmt), vpiCaseZ);
  EXPECT_EQ(vpi_get(vpiQualifier, &case_stmt),
            vpiUniqueQualifier | vpiPriorityQualifier);

  // A case statement written with no qualifier reports the "none" sentinel.
  VpiObject plain_case;
  plain_case.type = vpiCase;
  plain_case.case_type = vpiCaseExact;
  EXPECT_EQ(vpi_get(vpiQualifier, &plain_case), vpiNoQualifier);
}

// Diagram (case item -> vpiExpr -> pattern|expr): the classifier recognizes the
// kinds a case item's match expressions may reach - the pattern grouping
// members and ordinary expressions - while statements and unrelated objects are
// not conditions. This pins the grouping to the right children so the item's
// statement branch is never mistaken for a condition.
TEST_F(CasePattern, CaseItemConditionTypesAreClassified) {
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiAnyPattern));
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiTaggedPattern));
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiStructPattern));
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiPattern));
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiExpr));
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiOperation));  // an expr-class kind

  EXPECT_FALSE(VpiIsCaseItemConditionType(vpiIf));  // a statement, not a cond
  EXPECT_FALSE(VpiIsCaseItemConditionType(vpiBegin));  // a statement container
  EXPECT_FALSE(VpiIsCaseItemConditionType(vpiModule));
}

// Detail 1: a case item groups every case condition that branches to the same
// statement. The grouping helper returns the item's match-expression members -
// including a pattern - in order, and excludes the statement reached through
// the item's -> stmt edge; the shared statement itself is still reachable as
// the item's stmt.
TEST_F(CasePattern, CaseItemGroupsConditionsBranchingToOneStatement) {
  VpiObject item;
  item.type = vpiCaseItem;
  VpiObject c0;
  c0.type = vpiExpr;  // an ordinary condition expression
  VpiObject c1;
  c1.type = vpiTaggedPattern;  // a pattern condition
  VpiObject stmt;
  stmt.type = vpiStmt;  // the statement all conditions branch to (-> stmt edge)
  item.children = {&c0, &c1, &stmt};

  auto conditions = VpiCaseItemMatchExprs(&item);
  ASSERT_EQ(conditions.size(), 2u);
  EXPECT_EQ(conditions[0], &c0);
  EXPECT_EQ(conditions[1], &c1);

  // The statement is reached as the item's stmt, not as one of the conditions.
  EXPECT_EQ(VpiHandleC(vpiStmt, &item), &stmt);
}

// Detail 1 (via the public iteration): iterating the vpiExpr edge over a case
// item reaches every grouped condition, spanning both patterns and plain
// expressions - children whose own type is not vpiExpr that the generic
// type-match traversal would otherwise miss. The shared statement is not among
// them.
TEST_F(CasePattern, CaseItemMatchExprIterationReachesPatternsAndExprs) {
  VpiObject item;
  item.type = vpiCaseItem;
  VpiObject pattern;
  pattern.type = vpiStructPattern;
  VpiObject expr;
  expr.type = vpiOperation;
  VpiObject stmt;
  stmt.type = vpiAssignStmt;
  item.children = {&pattern, &expr, &stmt};

  VpiHandle it = ctx_.Iterate(vpiExpr, &item);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &pattern);
  EXPECT_EQ(ctx_.Scan(it), &expr);
  EXPECT_EQ(ctx_.Scan(it),
            nullptr);  // drains; the statement is not a condition
}

// Detail 2: vpi_iterate() returns NULL for the default case item, because there
// is no expression with the default case. The grouping helper likewise yields
// none. The flag enforces this even if the object carries stray children, so
// the default item is distinguished from a non-default item; a non-default item
// with conditions iterates to them.
TEST_F(CasePattern, DefaultCaseItemIteratesToNullAndGroupsNothing) {
  VpiObject default_item;
  default_item.type = vpiCaseItem;
  default_item.default_case_item = true;
  VpiObject stray;
  stray.type = vpiExpr;  // even a stray condition child does not count
  default_item.children = {&stray};

  EXPECT_TRUE(VpiCaseItemMatchExprs(&default_item).empty());
  EXPECT_EQ(ctx_.Iterate(vpiExpr, &default_item), nullptr);

  // A non-default item with a condition child does iterate to it.
  VpiObject item;
  item.type = vpiCaseItem;
  VpiObject c0;
  c0.type = vpiExpr;
  item.children = {&c0};
  VpiHandle it = ctx_.Iterate(vpiExpr, &item);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &c0);
  EXPECT_EQ(ctx_.Scan(it), nullptr);  // drains and frees the iterator
}

// Detail 2 (scope edge case): the default case item has no condition
// expression, but it still branches to a statement - the diagram's case item ->
// stmt edge applies to every item, default included. The NULL-iteration rule is
// therefore scoped to the vpiExpr edge: vpi_iterate(vpiExpr, default) is NULL
// while the item's statement stays reachable through vpiStmt. Without that
// scoping the guard would wrongly sever the default item from its statement.
TEST_F(CasePattern, DefaultCaseItemStillReachesItsStatement) {
  VpiObject default_item;
  default_item.type = vpiCaseItem;
  default_item.default_case_item = true;
  VpiObject stmt;
  stmt.type = vpiStmt;
  default_item.children = {&stmt};

  EXPECT_EQ(ctx_.Iterate(vpiExpr, &default_item), nullptr);  // no conditions
  EXPECT_EQ(VpiHandleC(vpiStmt, &default_item), &stmt);      // stmt still there
}

// Diagram scope (edge case): the vpiExpr edge that reaches patterns is the case
// item's edge, not the case statement's. Iterating vpiExpr over a case
// statement does not surface a pattern child (the generic type match a pattern
// does not satisfy), whereas the same pattern reached through a case item's
// vpiExpr edge is returned. This pins the case-item gating of the
// match-expression iteration, keeping the pattern-reaching behavior from
// leaking to other object kinds.
TEST_F(CasePattern, PatternReachIsSpecificToCaseItems) {
  VpiObject pattern;
  pattern.type = vpiTaggedPattern;

  // A case statement is not a case item: its vpiExpr iteration falls back to
  // the generic type match, which a pattern child does not satisfy.
  VpiObject case_stmt;
  case_stmt.type = vpiCase;
  case_stmt.children = {&pattern};
  EXPECT_EQ(ctx_.Iterate(vpiExpr, &case_stmt), nullptr);

  // Under a case item the same pattern is a reachable match expression.
  VpiObject item;
  item.type = vpiCaseItem;
  item.children = {&pattern};
  VpiHandle it = ctx_.Iterate(vpiExpr, &item);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &pattern);
  EXPECT_EQ(ctx_.Scan(it), nullptr);
}

}  // namespace
}  // namespace delta
