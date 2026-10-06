#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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

  EXPECT_EQ(vpi_get(vpiCaseType, VpiHandleOf(&case_stmt)), vpiCaseZ);
  EXPECT_EQ(vpi_get(vpiQualifier, VpiHandleOf(&case_stmt)),
            vpiUniqueQualifier | vpiPriorityQualifier);

  // A case statement written with no qualifier reports the "none" sentinel.
  VpiObject plain_case;
  plain_case.type = vpiCase;
  plain_case.case_type = vpiCaseExact;
  EXPECT_EQ(vpi_get(vpiQualifier, VpiHandleOf(&plain_case)), vpiNoQualifier);
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
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&item))), &stmt);
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
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&default_item))),
            &stmt);  // stmt still there
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

// Diagram (case -> vpiCondition -> expr): a case statement reaches the
// expression it selects on through vpiCondition, the tagged one-to-one edge
// §37.4.3 walks with vpi_handle(). The case items the diagram's other edge
// reaches are not it.
TEST_F(CasePattern, CaseStatementReachesTheExpressionItSelectsOn) {
  VpiObject selector;
  selector.type = vpiOperation;
  VpiObject item;
  item.type = vpiCaseItem;

  VpiObject case_stmt;
  case_stmt.type = vpiCase;
  case_stmt.children = {&item, &selector};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&case_stmt))),
            &selector);
}

// Diagram edge: a case statement written with no selector expression reaches
// none, rather than one of its case items.
TEST_F(CasePattern, CaseStatementWithNoSelectorReachesNoCondition) {
  VpiObject item;
  item.type = vpiCaseItem;

  VpiObject case_stmt;
  case_stmt.type = vpiCase;
  case_stmt.children = {&item};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&case_stmt)), nullptr);
}

// Diagram (pattern class membership): `pattern` is a class enclosure, so the
// kinds it groups are the three object definitions drawn inside it, and the
// class constant itself is not one of them (§37.4.1).
TEST_F(CasePattern, ThePatternClassGroupsTheThreePatternKinds) {
  EXPECT_TRUE(VpiIsPatternType(vpiAnyPattern));
  EXPECT_TRUE(VpiIsPatternType(vpiTaggedPattern));
  EXPECT_TRUE(VpiIsPatternType(vpiStructPattern));

  EXPECT_FALSE(VpiIsPatternType(vpiPattern));
  EXPECT_FALSE(VpiIsPatternType(vpiOperation));
}

// Diagram (tagged pattern -> pattern): a tagged pattern reaches the pattern it
// tags. The arrow names the `pattern` class, so what comes back is an object of
// a kind that class groups - the tagged pattern's typespec, drawn by its other
// arrow, is not one.
TEST_F(CasePattern, ATaggedPatternReachesThePatternItTags) {
  VpiObject inner;
  inner.type = vpiStructPattern;
  VpiObject typespec;
  typespec.type = vpiTypespec;

  VpiObject tagged;
  tagged.type = vpiTaggedPattern;
  tagged.name = "kind";
  tagged.children = {&typespec, &inner};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPattern, VpiHandleOf(&tagged))), &inner);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTypespec, VpiHandleOf(&tagged))),
            &typespec);
  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&tagged)), "kind");
}

// Diagram (struct pattern -> pattern): a struct pattern reaches the pattern of
// its member the same way, and a pattern holding none reaches none.
TEST_F(CasePattern, AStructPatternReachesItsMemberPattern) {
  VpiObject member;
  member.type = vpiAnyPattern;

  VpiObject struct_pattern;
  struct_pattern.type = vpiStructPattern;
  struct_pattern.children = {&member};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPattern, VpiHandleOf(&struct_pattern))),
            &member);

  VpiObject leaf;
  leaf.type = vpiAnyPattern;
  EXPECT_EQ(vpi_handle(vpiPattern, VpiHandleOf(&leaf)), nullptr);
}

// The case statements of a run: those a design's procedures write, built from
// the elaborated design rather than by hand (#5005).
class CaseStatementsOfARun : public VpiDesignRun {
 protected:
  static std::vector<vpiHandle> Scanned(vpiHandle it) {
    std::vector<vpiHandle> objects;
    while (vpiHandle obj = it ? vpi_scan(it) : nullptr) objects.push_back(obj);
    return objects;
  }
};

// A case reaches its type, the expression it selects on, and an item per case
// item, each grouping its expressions and reaching its statement; the default
// item groups none (detail 2).
TEST_F(CaseStatementsOfARun, ACaseIsAnObjectOfTheRun) {
  Run("module top; int a, b;\n"
      "  initial casez (a) 1, 2: b = 1; default: b = 0; endcase\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs =
      Scanned(vpi_iterate(vpiProcess, By("top")));
  ASSERT_EQ(kProcs.size(), 1U);
  vpiHandle selection = vpi_handle(vpiStmt, kProcs[0]);
  ASSERT_NE(selection, nullptr);
  EXPECT_EQ(vpi_get(vpiType, selection), vpiCase);
  EXPECT_EQ(vpi_get(vpiCaseType, selection), vpiCaseZ);
  EXPECT_EQ(vpi_get(vpiQualifier, selection), vpiNoQualifier);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, selection)),
            VpiObjectOf(By("top.a")));
  const std::vector<vpiHandle> kItems =
      Scanned(vpi_iterate(vpiCaseItem, selection));
  ASSERT_EQ(kItems.size(), 2U);
  EXPECT_EQ(Scanned(vpi_iterate(vpiExpr, kItems[0])).size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiStmt, kItems[0])), vpiAssignment);
  EXPECT_EQ(vpi_iterate(vpiExpr, kItems[1]), nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiStmt, kItems[1])), vpiAssignment);
}

// A unique or priority keyword, and a case inside, are the case's qualifier;
// a plain case keyword is an exact match.
TEST_F(CaseStatementsOfARun, ACaseReportsItsQualifier) {
  Run("module top; int a, b;\n"
      "  initial unique case (a) 0: b = 1; endcase\n"
      "  initial priority case (a) inside 1: b = 1; endcase\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs =
      Scanned(vpi_iterate(vpiProcess, By("top")));
  ASSERT_EQ(kProcs.size(), 2U);
  vpiHandle unique = vpi_handle(vpiStmt, kProcs[0]);
  vpiHandle inside = vpi_handle(vpiStmt, kProcs[1]);
  ASSERT_NE(unique, nullptr);
  ASSERT_NE(inside, nullptr);
  EXPECT_EQ(vpi_get(vpiCaseType, unique), vpiCaseExact);
  EXPECT_EQ(vpi_get(vpiQualifier, unique), vpiUniqueQualifier);
  EXPECT_EQ(vpi_get(vpiQualifier, inside),
            vpiPriorityQualifier | vpiInsideQualifier);
}

// Annex M gives vpiQualifier no unique0 bit; §12.5.3 makes a unique0-case
// assert the same absence of overlap a unique-case does, so a case written
// with unique0 reports the unique qualifier, beside the inside bit when it
// matches by set membership (#5063).
TEST_F(CaseStatementsOfARun, AUnique0CaseReportsTheUniqueQualifier) {
  Run("module top; int a, b;\n"
      "  initial unique0 case (a) 0: b = 1; endcase\n"
      "  initial unique0 case (a) inside 1: b = 1; endcase\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs =
      Scanned(vpi_iterate(vpiProcess, By("top")));
  ASSERT_EQ(kProcs.size(), 2U);
  vpiHandle exact = vpi_handle(vpiStmt, kProcs[0]);
  vpiHandle inside = vpi_handle(vpiStmt, kProcs[1]);
  ASSERT_NE(exact, nullptr);
  ASSERT_NE(inside, nullptr);
  EXPECT_EQ(vpi_get(vpiQualifier, exact), vpiUniqueQualifier);
  EXPECT_EQ(vpi_get(vpiQualifier, inside),
            vpiUniqueQualifier | vpiInsideQualifier);
}

}  // namespace
}  // namespace delta
