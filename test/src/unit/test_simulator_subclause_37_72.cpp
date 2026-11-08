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

class CasePattern : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(CasePattern, CaseStatementReportsCaseTypeAndQualifier) {
  VpiObject case_stmt;
  case_stmt.type = vpiCase;
  case_stmt.case_type = vpiCaseZ;
  case_stmt.qualifier = vpiUniqueQualifier | vpiPriorityQualifier;

  EXPECT_EQ(vpi_get(vpiCaseType, VpiHandleOf(&case_stmt)), vpiCaseZ);
  EXPECT_EQ(vpi_get(vpiQualifier, VpiHandleOf(&case_stmt)),
            vpiUniqueQualifier | vpiPriorityQualifier);

  VpiObject plain_case;
  plain_case.type = vpiCase;
  plain_case.case_type = vpiCaseExact;
  EXPECT_EQ(vpi_get(vpiQualifier, VpiHandleOf(&plain_case)), vpiNoQualifier);
}

TEST_F(CasePattern, CaseItemConditionTypesAreClassified) {
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiAnyPattern));
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiTaggedPattern));
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiStructPattern));
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiExpr));
  EXPECT_TRUE(VpiIsCaseItemConditionType(vpiOperation));

  EXPECT_FALSE(VpiIsCaseItemConditionType(vpiIf));
  EXPECT_FALSE(VpiIsCaseItemConditionType(vpiBegin));
  EXPECT_FALSE(VpiIsCaseItemConditionType(vpiModule));
}

TEST_F(CasePattern, CaseItemGroupsConditionsBranchingToOneStatement) {
  VpiObject item;
  item.type = vpiCaseItem;
  VpiObject c0;
  c0.type = vpiExpr;
  VpiObject c1;
  c1.type = vpiTaggedPattern;
  VpiObject stmt;
  stmt.type = vpiStmt;
  item.children = {&c0, &c1, &stmt};

  auto conditions = VpiCaseItemMatchExprs(&item);
  ASSERT_EQ(conditions.size(), 2u);
  EXPECT_EQ(conditions[0], &c0);
  EXPECT_EQ(conditions[1], &c1);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&item))), &stmt);
}

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
  EXPECT_EQ(ctx_.Scan(it), nullptr);
}

TEST_F(CasePattern, DefaultCaseItemIteratesToNullAndGroupsNothing) {
  VpiObject default_item;
  default_item.type = vpiCaseItem;
  default_item.default_case_item = true;
  VpiObject stray;
  stray.type = vpiExpr;
  default_item.children = {&stray};

  EXPECT_TRUE(VpiCaseItemMatchExprs(&default_item).empty());
  EXPECT_EQ(ctx_.Iterate(vpiExpr, &default_item), nullptr);

  VpiObject item;
  item.type = vpiCaseItem;
  VpiObject c0;
  c0.type = vpiExpr;
  item.children = {&c0};
  VpiHandle it = ctx_.Iterate(vpiExpr, &item);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &c0);
  EXPECT_EQ(ctx_.Scan(it), nullptr);
}

TEST_F(CasePattern, DefaultCaseItemStillReachesItsStatement) {
  VpiObject default_item;
  default_item.type = vpiCaseItem;
  default_item.default_case_item = true;
  VpiObject stmt;
  stmt.type = vpiStmt;
  default_item.children = {&stmt};

  EXPECT_EQ(ctx_.Iterate(vpiExpr, &default_item), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&default_item))),
            &stmt);
}

TEST_F(CasePattern, PatternReachIsSpecificToCaseItems) {
  VpiObject pattern;
  pattern.type = vpiTaggedPattern;

  VpiObject case_stmt;
  case_stmt.type = vpiCase;
  case_stmt.children = {&pattern};
  EXPECT_EQ(ctx_.Iterate(vpiExpr, &case_stmt), nullptr);

  VpiObject item;
  item.type = vpiCaseItem;
  item.children = {&pattern};
  VpiHandle it = ctx_.Iterate(vpiExpr, &item);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &pattern);
  EXPECT_EQ(ctx_.Scan(it), nullptr);
}

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

TEST_F(CasePattern, CaseStatementWithNoSelectorReachesNoCondition) {
  VpiObject item;
  item.type = vpiCaseItem;

  VpiObject case_stmt;
  case_stmt.type = vpiCase;
  case_stmt.children = {&item};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&case_stmt)), nullptr);
}

TEST_F(CasePattern, ThePatternClassGroupsTheThreePatternKinds) {
  EXPECT_TRUE(VpiIsPatternType(vpiAnyPattern));
  EXPECT_TRUE(VpiIsPatternType(vpiTaggedPattern));
  EXPECT_TRUE(VpiIsPatternType(vpiStructPattern));

  EXPECT_FALSE(VpiIsPatternType(vpiPattern));
  EXPECT_FALSE(VpiIsPatternType(vpiOperation));
}

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

class CaseStatementsOfARun : public VpiDesignRun {
 protected:
  static std::vector<vpiHandle> Scanned(vpiHandle it) {
    std::vector<vpiHandle> objects;
    while (vpiHandle obj = it ? vpi_scan(it) : nullptr) objects.push_back(obj);
    return objects;
  }

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
  EXPECT_EQ(kinds, (std::vector<int>{vpiIntTypespec, vpiBitTypespec,
                                     vpiVoidTypespec}));
  const std::vector<std::vector<vpiHandle>> kSelected = ItemConditions(1);
  ASSERT_EQ(kSelected.size(), 1U);
  ASSERT_EQ(kSelected[0].size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kSelected[0][0]), vpiTaggedPattern);
  EXPECT_EQ(vpi_handle(vpiTypespec, kSelected[0][0]), nullptr);
}

TEST_F(CaseStatementsOfARun, APatternWrittenAsAnExpressionIsReached) {
  Run("module top;\n"
      "  typedef union tagged { int V; void N; } u_t;\n"
      "  typedef struct { int a; int b; } s_t;\n"
      "  u_t u; s_t s; int r;\n"
      "  initial case (u) matches\n"
      "    tagged V 5: r = 1;\n"
      "  endcase\n"
      "  initial case (s) matches\n"
      "    '{a: 5, b: .*}: r = 2;\n"
      "  endcase\n"
      "endmodule\n");
  const std::vector<std::vector<vpiHandle>> kTagged = ItemConditions(0);
  ASSERT_EQ(kTagged.size(), 1U);
  ASSERT_EQ(kTagged[0].size(), 1U);
  vpiHandle constant = vpi_handle(vpiPattern, kTagged[0][0]);
  ASSERT_NE(constant, nullptr);
  EXPECT_EQ(vpi_get(vpiType, constant), vpiConstant);
  const std::vector<std::vector<vpiHandle>> kStruct = ItemConditions(1);
  ASSERT_EQ(kStruct.size(), 1U);
  ASSERT_EQ(kStruct[0].size(), 1U);
  const std::vector<vpiHandle> kMembers =
      Scanned(vpi_iterate(vpiOperand, kStruct[0][0]));
  ASSERT_EQ(kMembers.size(), 2U);
  vpiHandle member = vpi_handle(vpiPattern, kMembers[0]);
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(vpi_get(vpiType, member), vpiConstant);
}

}  // namespace
}  // namespace delta
