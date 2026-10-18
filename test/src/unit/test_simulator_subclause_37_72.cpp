#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
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

  // The conditions of each case item of the case statement the process
  // `index` of `top` is, item by item.
  static std::vector<std::vector<vpiHandle>> ItemConditions(size_t index) {
    const std::vector<vpiHandle> kProcs =
        Scanned(vpi_iterate(vpiProcess, By("top")));
    std::vector<std::vector<vpiHandle>> conditions;
    if (index >= kProcs.size()) return conditions;
    for (vpiHandle item : Scanned(
             vpi_iterate(vpiCaseItem, vpi_handle(vpiStmt, kProcs[index])))) {
      conditions.push_back(Scanned(vpi_iterate(vpiExpr, item)));
    }
    return conditions;
  }

  // The kind and the name, "" for none, of each operand of `op`.
  static std::vector<std::pair<int, std::string>> KindsAndNames(vpiHandle op) {
    std::vector<std::pair<int, std::string>> shown;
    for (vpiHandle operand : Scanned(vpi_iterate(vpiOperand, op))) {
      const char* name = vpi_get_str(vpiName, operand);
      shown.emplace_back(vpi_get(vpiType, operand),
                         name == nullptr ? "" : name);
    }
    return shown;
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

// §37.72: no object reaches no pattern, no case condition and no match
// expressions; and a condition-kind child written as a statement is the
// item's statement, not one of its conditions (detail 1).
TEST(CaseModel, NoObjectAndStatementChildrenReachNoConditions) {
  EXPECT_EQ(VpiPatternOf(nullptr), nullptr);
  EXPECT_EQ(VpiCaseConditionExpr(nullptr), nullptr);
  EXPECT_TRUE(VpiCaseItemMatchExprs(nullptr).empty());
  VpiObject stmt;
  stmt.type = vpiOperation;
  stmt.written_as_stmt = true;
  VpiObject item;
  item.type = vpiCaseItem;
  item.children = {&stmt};
  EXPECT_TRUE(VpiCaseItemMatchExprs(&item).empty());
}

// A case matches item's patterns are pattern objects: `tagged V .n` a tagged
// pattern named after its member, reaching the any pattern `.n` named after
// the variable it binds; `tagged N` a tagged pattern reaching none; and `.*`
// an any pattern binding no name.
TEST_F(CaseStatementsOfARun, ACaseMatchesItemReachesItsPatterns) {
  Run("module top;\n"
      "  typedef union tagged { int V; void N; } u_t;\n"
      "  u_t u; int r;\n"
      "  initial case (u) matches\n"
      "    tagged V .n: r = n;\n"
      "    tagged N: r = 0;\n"
      "    .*: r = 1;\n"
      "  endcase\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs =
      Scanned(vpi_iterate(vpiProcess, By("top")));
  ASSERT_EQ(kProcs.size(), 1U);
  const std::vector<vpiHandle> kItems =
      Scanned(vpi_iterate(vpiCaseItem, vpi_handle(vpiStmt, kProcs[0])));
  ASSERT_EQ(kItems.size(), 3U);
  const std::vector<vpiHandle> kFirst =
      Scanned(vpi_iterate(vpiExpr, kItems[0]));
  ASSERT_EQ(kFirst.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kFirst[0]), vpiTaggedPattern);
  EXPECT_STREQ(vpi_get_str(vpiName, kFirst[0]), "V");
  vpiHandle bound = vpi_handle(vpiPattern, kFirst[0]);
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bound), vpiAnyPattern);
  EXPECT_STREQ(vpi_get_str(vpiName, bound), "n");
  const std::vector<vpiHandle> kSecond =
      Scanned(vpi_iterate(vpiExpr, kItems[1]));
  ASSERT_EQ(kSecond.size(), 1U);
  EXPECT_STREQ(vpi_get_str(vpiName, kSecond[0]), "N");
  EXPECT_EQ(vpi_handle(vpiPattern, kSecond[0]), nullptr);
  const std::vector<vpiHandle> kThird =
      Scanned(vpi_iterate(vpiExpr, kItems[2]));
  ASSERT_EQ(kThird.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kThird[0]), vpiAnyPattern);
}

// Detail 1 with §37.59 detail 6 and §12.6: a structure pattern is one case
// condition, an assignment pattern operation. Written with member names, its
// operands are a struct pattern per member of the structure in declaration
// order, each named after its member and reaching the pattern written for it,
// an omitted one an any pattern binding no name; written positionally, the
// member patterns themselves, a constant among them as the expression it is.
// A case expression reaching no typespec, a select of an array (#7019), gives
// a positional pattern those operands too (#7270).
TEST_F(CaseStatementsOfARun, AStructurePatternIsAnAssignmentPatternOperation) {
  Run("module top;\n"
      "  typedef struct { int a; int b; int c; } s_t;\n"
      "  s_t s; s_t sa [2]; int r;\n"
      "  initial case (s) matches\n"
      "    '{b: .y, a: .x}: r = x + y;\n"
      "    '{.x, .*, .z}: r = x + z;\n"
      "  endcase\n"
      "  initial case (sa[0]) matches\n"
      "    '{.x, 1, .z}: r = x;\n"
      "  endcase\n"
      "endmodule\n");
  const std::vector<std::vector<vpiHandle>> kItems = ItemConditions(0);
  ASSERT_EQ(kItems.size(), 2U);
  ASSERT_EQ(kItems[0].size(), 1U);
  vpiHandle keyed = kItems[0][0];
  EXPECT_EQ(vpi_get(vpiType, keyed), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, keyed), vpiAssignmentPatternOp);
  const std::vector<vpiHandle> kMembers =
      Scanned(vpi_iterate(vpiOperand, keyed));
  ASSERT_EQ(kMembers.size(), 3U);
  const std::vector<std::pair<int, std::string>> kStruct{
      {vpiStructPattern, "a"},
      {vpiStructPattern, "b"},
      {vpiStructPattern, "c"}};
  EXPECT_EQ(KindsAndNames(keyed), kStruct);
  std::vector<std::pair<int, std::string>> bound;
  for (vpiHandle member : kMembers) {
    vpiHandle pattern = vpi_handle(vpiPattern, member);
    ASSERT_NE(pattern, nullptr);
    const char* name = vpi_get_str(vpiName, pattern);
    bound.emplace_back(vpi_get(vpiType, pattern), name == nullptr ? "" : name);
  }
  const std::vector<std::pair<int, std::string>> kAny{
      {vpiAnyPattern, "x"}, {vpiAnyPattern, "y"}, {vpiAnyPattern, ""}};
  EXPECT_EQ(bound, kAny);
  ASSERT_EQ(kItems[1].size(), 1U);
  EXPECT_EQ(vpi_get(vpiOpType, kItems[1][0]), vpiAssignmentPatternOp);
  const std::vector<std::pair<int, std::string>> kPositional{
      {vpiAnyPattern, "x"}, {vpiAnyPattern, ""}, {vpiAnyPattern, "z"}};
  EXPECT_EQ(KindsAndNames(kItems[1][0]), kPositional);
  const std::vector<std::vector<vpiHandle>> kSelected = ItemConditions(1);
  ASSERT_EQ(kSelected.size(), 1U);
  ASSERT_EQ(kSelected[0].size(), 1U);
  EXPECT_EQ(
      KindsAndNames(kSelected[0][0]),
      (std::vector<std::pair<int, std::string>>{
          {vpiAnyPattern, "x"}, {vpiConstant, ""}, {vpiAnyPattern, "z"}}));
}

// The tagged pattern -> typespec arrow: a tagged pattern reaches the typespec
// of the member it is tagged with, int's for V and a bit typespec for the
// bit [3:0] W; none for the void N, which has no typespec yet (#7085), nor
// where the case expression reaches no typespec, a select of an array (#7019)
// (#7271).
TEST_F(CaseStatementsOfARun, ATaggedPatternReachesItsMembersTypespec) {
  Run("module top;\n"
      "  typedef union tagged { int V; bit [3:0] W; void N; } u_t;\n"
      "  u_t u; u_t ua [2]; int r;\n"
      "  initial case (u) matches\n"
      "    tagged V .n: r = n;\n"
      "    tagged W .w: r = w;\n"
      "    tagged N: r = 0;\n"
      "  endcase\n"
      "  initial case (ua[0]) matches\n"
      "    tagged V .n: r = n;\n"
      "  endcase\n"
      "endmodule\n");
  const std::vector<std::vector<vpiHandle>> kItems = ItemConditions(0);
  ASSERT_EQ(kItems.size(), 3U);
  std::vector<int> kinds;
  for (const std::vector<vpiHandle>& conditions : kItems) {
    ASSERT_EQ(conditions.size(), 1U);
    vpiHandle typespec = vpi_handle(vpiTypespec, conditions[0]);
    kinds.push_back(typespec == nullptr ? 0 : vpi_get(vpiType, typespec));
  }
  EXPECT_EQ(kinds, (std::vector<int>{vpiIntTypespec, vpiBitTypespec, 0}));
  const std::vector<std::vector<vpiHandle>> kSelected = ItemConditions(1);
  ASSERT_EQ(kSelected.size(), 1U);
  ASSERT_EQ(kSelected[0].size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kSelected[0][0]), vpiTaggedPattern);
  EXPECT_EQ(vpi_handle(vpiTypespec, kSelected[0][0]), nullptr);
}

}  // namespace
}  // namespace delta
