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

constexpr const char* kCaseForms =
    "module top;\n"
    "  typedef union tagged { int V; void N; } u_t;\n"
    "  typedef struct { int p; int q; } in_t;\n"
    "  typedef struct { u_t a; int b; } st_t;\n"
    "  typedef struct { in_t a; int b; } sn_t;\n"
    "  typedef union tagged { in_t S; u_t T; void N; } w_t;\n"
    "  u_t u; st_t st; sn_t sn; w_t w; int a, b, r; logic [7:0] v;\n"
    "  in_t sa [2];\n"
    "  function int f(int x); return x; endfunction\n"
    "  initial casez (a) 1, 2: r = 1; endcase\n"
    "  initial case (a) inside 0, [2:4]: r = 1; endcase\n"
    "  initial case (u) matches tagged V .n &&& (n > 0): r = n; endcase\n"
    "  initial case (st) matches '{a: tagged V .n, b: .*}: r = n; endcase\n"
    "  initial case (sn) matches '{a: '{p: .x, q: .*}, b: .*}: r = x; endcase\n"
    "  initial case (w) matches tagged S '{p: .x, q: .*}: r = x; endcase\n"
    "  initial case (w) matches tagged T tagged V .n: r = n; endcase\n"
    "  initial case (a) inside 1: r = 1; default: r = 2; endcase\n"
    "  initial casex (a) 1: r = 1; endcase\n"
    "  initial case (u) matches tagged N: r = 0; default: r = 1; endcase\n"
    "  initial priority case (a) 1: r = 1; default: r = 2; endcase\n"
    "  initial unique case (u) matches tagged N: r = 0; default: r = 1;\n"
    "  endcase\n"
    "  initial priority case (u) matches tagged N: r = 0; default: r = 1;\n"
    "  endcase\n"
    "  initial case (a + b) 1: r = 1; endcase\n"
    "  initial case (v[0]) 1: r = 1; endcase\n"
    "  initial case (v[3:0]) 1: r = 1; endcase\n"
    "  initial case (f(a)) 1: r = 1; endcase\n"
    "  initial case (sa[0]) matches '{p: .x, q: .*}: r = x; endcase\n"
    "endmodule\n";

class CaseFormsOfARun : public CaseStatementsOfARun {
 protected:
  void SetUp() override {
    CaseStatementsOfARun::SetUp();
    Run(kCaseForms);
  }

  static vpiHandle CaseAt(size_t n) {
    const std::vector<vpiHandle> kProcs =
        Scanned(vpi_iterate(vpiProcess, By("top")));
    return n < kProcs.size() ? vpi_handle(vpiStmt, kProcs[n]) : nullptr;
  }

  static vpiHandle SoleCondition(size_t n) {
    const std::vector<std::vector<vpiHandle>> kItems = ItemConditions(n);
    return kItems.size() == 1 && kItems[0].size() == 1 ? kItems[0][0] : nullptr;
  }

  static void ExpectKindAndQualifier(size_t n, int case_type, int qualifier) {
    vpiHandle selection = CaseAt(n);
    ASSERT_NE(selection, nullptr);
    EXPECT_EQ(vpi_get(vpiCaseType, selection), case_type);
    EXPECT_EQ(vpi_get(vpiQualifier, selection), qualifier);
  }

  static void ExpectDefaultLast(size_t n) {
    vpiHandle selection = CaseAt(n);
    ASSERT_NE(selection, nullptr);
    const std::vector<vpiHandle> kItems =
        Scanned(vpi_iterate(vpiCaseItem, selection));
    ASSERT_EQ(kItems.size(), 2U);
    EXPECT_NE(vpi_iterate(vpiExpr, kItems[0]), nullptr);
    EXPECT_EQ(vpi_iterate(vpiExpr, kItems[1]), nullptr);
    vpiHandle body = vpi_handle(vpiStmt, kItems[1]);
    ASSERT_NE(body, nullptr);
    EXPECT_EQ(vpi_get(vpiType, body), vpiAssignment);
  }

  static vpiHandle ConditionAt(size_t n) {
    vpiHandle selection = CaseAt(n);
    return selection == nullptr ? nullptr : vpi_handle(vpiCondition, selection);
  }
};

TEST_F(CaseFormsOfARun, AnItemsExpressionsComeInTheOrderWritten) {
  const std::vector<std::vector<vpiHandle>> kItems = ItemConditions(0);
  ASSERT_EQ(kItems.size(), 1U);
  ASSERT_EQ(kItems[0].size(), 2U);
  EXPECT_EQ(IntegerOf(kItems[0][0]), 1);
  EXPECT_EQ(IntegerOf(kItems[0][1]), 2);
}

TEST_F(CaseFormsOfARun, ACaseInsideRangeIsOneExpressionBesideAValue) {
  const std::vector<std::vector<vpiHandle>> kItems = ItemConditions(1);
  ASSERT_EQ(kItems.size(), 1U);
  ASSERT_EQ(kItems[0].size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kItems[0][0]), vpiConstant);
  EXPECT_EQ(IntegerOf(kItems[0][0]), 0);
  EXPECT_NE(vpi_get(vpiType, kItems[0][1]), vpiConstant);
}

TEST_F(CaseFormsOfARun, DISABLED_AGuardedPatternGivesThePatternAndTheGuard) {
  const std::vector<std::vector<vpiHandle>> kItems = ItemConditions(2);
  ASSERT_EQ(kItems.size(), 1U);
  ASSERT_EQ(kItems[0].size(), 2U);
  EXPECT_EQ(vpi_get(vpiType, kItems[0][0]), vpiTaggedPattern);
  EXPECT_STREQ(vpi_get_str(vpiName, kItems[0][0]), "V");
  EXPECT_EQ(OpOf(kItems[0][1]), vpiGtOp);
}

TEST_F(CaseFormsOfARun, AStructMemberPatternCanBeATaggedPattern) {
  vpiHandle keyed = SoleCondition(3);
  ASSERT_NE(keyed, nullptr);
  const std::vector<vpiHandle> kMembers =
      Scanned(vpi_iterate(vpiOperand, keyed));
  ASSERT_EQ(kMembers.size(), 2U);
  EXPECT_STREQ(vpi_get_str(vpiName, kMembers[0]), "a");
  vpiHandle tagged = vpi_handle(vpiPattern, kMembers[0]);
  ASSERT_NE(tagged, nullptr);
  EXPECT_EQ(vpi_get(vpiType, tagged), vpiTaggedPattern);
  EXPECT_STREQ(vpi_get_str(vpiName, tagged), "V");
}

TEST_F(CaseFormsOfARun, AStructMemberPatternCanBeAStructurePattern) {
  vpiHandle keyed = SoleCondition(4);
  ASSERT_NE(keyed, nullptr);
  const std::vector<vpiHandle> kMembers =
      Scanned(vpi_iterate(vpiOperand, keyed));
  ASSERT_EQ(kMembers.size(), 2U);
  vpiHandle inner = vpi_handle(vpiPattern, kMembers[0]);
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, inner), vpiAssignmentPatternOp);
  EXPECT_EQ(KindsAndNames(inner),
            (std::vector<std::pair<int, std::string>>{
                {vpiStructPattern, "p"}, {vpiStructPattern, "q"}}));
}

TEST_F(CaseFormsOfARun, ATaggedPatternCanTagAStructurePattern) {
  vpiHandle tagged = SoleCondition(5);
  ASSERT_NE(tagged, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, tagged), "S");
  vpiHandle inner = vpi_handle(vpiPattern, tagged);
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, inner), vpiAssignmentPatternOp);
  EXPECT_EQ(KindsAndNames(inner),
            (std::vector<std::pair<int, std::string>>{
                {vpiStructPattern, "p"}, {vpiStructPattern, "q"}}));
}

TEST_F(CaseFormsOfARun, ATaggedPatternCanTagAnotherTaggedPattern) {
  vpiHandle outer = SoleCondition(6);
  ASSERT_NE(outer, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, outer), "T");
  vpiHandle inner = vpi_handle(vpiPattern, outer);
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inner), vpiTaggedPattern);
  EXPECT_STREQ(vpi_get_str(vpiName, inner), "V");
  vpiHandle typespec = vpi_handle(vpiTypespec, inner);
  ASSERT_NE(typespec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, typespec), vpiIntTypespec);
  vpiHandle bound = vpi_handle(vpiPattern, inner);
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(vpi_get(vpiType, bound), vpiAnyPattern);
  EXPECT_STREQ(vpi_get_str(vpiName, bound), "n");
}

TEST_F(CaseFormsOfARun, APlainCaseInsideIsExactAndInsideQualified) {
  ExpectKindAndQualifier(7, vpiCaseExact, vpiInsideQualifier);
}

TEST_F(CaseFormsOfARun, ACasexReportsTheXCaseType) {
  ExpectKindAndQualifier(8, vpiCaseX, vpiNoQualifier);
}

TEST_F(CaseFormsOfARun, ACaseMatchesIsExactAndTaggedQualified) {
  ExpectKindAndQualifier(9, vpiCaseExact, vpiTaggedQualifier);
}

TEST_F(CaseFormsOfARun, APriorityCaseReportsThePriorityQualifierAlone) {
  ExpectKindAndQualifier(10, vpiCaseExact, vpiPriorityQualifier);
}

TEST_F(CaseFormsOfARun, AKeywordOnACaseMatchesJoinsTheTaggedQualifier) {
  ExpectKindAndQualifier(11, vpiCaseExact,
                         vpiUniqueQualifier | vpiTaggedQualifier);
  ExpectKindAndQualifier(12, vpiCaseExact,
                         vpiPriorityQualifier | vpiTaggedQualifier);
}

TEST_F(CaseFormsOfARun, TheDefaultOfACaseInsideHasNoExpressions) {
  ExpectDefaultLast(7);
}

TEST_F(CaseFormsOfARun, TheDefaultOfACaseMatchesHasNoExpressions) {
  ExpectDefaultLast(9);
}

TEST_F(CaseFormsOfARun, AnOperationSelectorIsTheOperation) {
  vpiHandle condition = ConditionAt(13);
  EXPECT_EQ(OpOf(condition), vpiAddOp);
  const std::vector<vpiHandle> kSides = OperandsOf(condition);
  ASSERT_EQ(kSides.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kSides[0]), VpiObjectOf(By("top.a")));
  EXPECT_EQ(VpiObjectOf(kSides[1]), VpiObjectOf(By("top.b")));
}

TEST_F(CaseFormsOfARun, ABitSelectorIsABitOfItsVector) {
  vpiHandle condition = ConditionAt(14);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiVarBit);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, condition)),
            VpiObjectOf(By("top.v")));
}

TEST_F(CaseFormsOfARun, APartSelectorIsAPartSelect) {
  vpiHandle condition = ConditionAt(15);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiPartSelect);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiLeftRange, condition)), 3);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRightRange, condition)), 0);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, condition)),
            VpiObjectOf(By("top.v")));
}

TEST_F(CaseFormsOfARun, ACallSelectorIsTheCall) {
  vpiHandle condition = ConditionAt(16);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiFuncCall);
  EXPECT_EQ(CalleeOf(condition), "f");
}

TEST_F(CaseFormsOfARun, AnArrayElementSelectorIsThatElement) {
  vpiHandle element = By("top.sa[0]");
  ASSERT_NE(element, nullptr);
  EXPECT_EQ(VpiObjectOf(ConditionAt(17)), VpiObjectOf(element));
}

TEST_F(CaseStatementsOfARun, ACaseInsideToleranceRangeIsOneExpression) {
  Run("module top; int a, r;\n"
      "  initial case (a) inside 0, [5 +/- 1]: r = 1; endcase\n"
      "  initial case (a) inside 0, [5 +%- 20]: r = 1; endcase\n"
      "endmodule\n");
  for (size_t n = 0; n < 2; ++n) {
    const std::vector<std::vector<vpiHandle>> kItems = ItemConditions(n);
    ASSERT_EQ(kItems.size(), 1U) << n;
    ASSERT_EQ(kItems[0].size(), 2U) << n;
    EXPECT_EQ(IntegerOf(kItems[0][0]), 0) << n;
    EXPECT_NE(vpi_get(vpiType, kItems[0][1]), vpiConstant) << n;
  }
}

class CasesInEachPlace : public CaseStatementsOfARun {
 protected:
  static vpiHandle CaseIn(const char* scope, int kind, const char* name) {
    vpiHandle owner = nullptr;
    if (kind == vpiProcess) {
      const std::vector<vpiHandle> kProcs =
          Scanned(vpi_iterate(vpiProcess, By(scope)));
      owner = kProcs.size() == 1 ? kProcs[0] : nullptr;
    } else if (kind == vpiMethods) {
      owner = Named(vpiMethods, Named(vpiClassDefn, By(scope), "C"), name);
    } else {
      owner = Named(kind, By(scope), name);
    }
    vpiHandle stmt = owner == nullptr ? nullptr : vpi_handle(vpiStmt, owner);
    if (stmt != nullptr && vpi_get(vpiType, stmt) == vpiEventControl) {
      stmt = vpi_handle(vpiStmt, stmt);
    }
    return stmt;
  }
};

TEST_F(CasesInEachPlace, ACaseInEachPlaceIteratesItsItems) {
  Run("package pk; int a, i;\n"
      "  task pt; case (a) 1: i = 1; default: i = 2; endcase endtask\n"
      "endpackage\n"
      "interface ifc; int a, i;\n"
      "  initial case (a) 1: i = 1; default: i = 2; endcase\n"
      "endinterface\n"
      "program prg; int a, i;\n"
      "  initial case (a) 1: i = 1; default: i = 2; endcase\n"
      "endprogram\n"
      "module mal; bit c; int a, i;\n"
      "  always @(c) case (a) 1: i = 1; default: i = 2; endcase\n"
      "endmodule\n"
      "module mac; int a, i;\n"
      "  always_comb case (a) 1: i = 1; default: i = 2; endcase\n"
      "endmodule\n"
      "module maf; bit c; int a, i;\n"
      "  always_ff @(posedge c) case (a) 1: i <= 1; default: i <= 2; endcase\n"
      "endmodule\n"
      "module mat; int a, i;\n"
      "  always_latch case (a) 1: i = 1; default: i = 2; endcase\n"
      "endmodule\n"
      "module mfi; int a, i;\n"
      "  final case (a) 1: i = 1; default: i = 2; endcase\n"
      "endmodule\n"
      "module top; int a, i; ifc i0(); prg p0(); mal al(); mac ac();\n"
      "  maf af(); mat at(); mfi fi();\n"
      "  class C; int a, i;\n"
      "    task ct; case (a) 1: i = 1; default: i = 2; endcase endtask\n"
      "  endclass\n"
      "  task tk; case (a) 1: i = 1; default: i = 2; endcase endtask\n"
      "  function void fn; case (a) 1: i = 1; default: i = 2; endcase\n"
      "  endfunction\n"
      "endmodule\n");
  const struct {
    const char* scope;
    int kind;
    const char* name;
  } kPlaces[] = {
      {"pk", vpiTask, "pt"},      {"top.i0", vpiProcess, ""},
      {"top.p0", vpiProcess, ""}, {"top.al", vpiProcess, ""},
      {"top.ac", vpiProcess, ""}, {"top.af", vpiProcess, ""},
      {"top.at", vpiProcess, ""}, {"top.fi", vpiProcess, ""},
      {"top", vpiMethods, "ct"},  {"top", vpiTask, "tk"},
      {"top", vpiFunction, "fn"},
  };
  for (const auto& place : kPlaces) {
    const std::string kWhere = std::string(place.scope) + " " + place.name;
    vpiHandle selection = CaseIn(place.scope, place.kind, place.name);
    ASSERT_NE(selection, nullptr) << kWhere;
    EXPECT_EQ(vpi_get(vpiType, selection), vpiCase) << kWhere;
    const std::vector<vpiHandle> kItems =
        Scanned(vpi_iterate(vpiCaseItem, selection));
    ASSERT_EQ(kItems.size(), 2U) << kWhere;
    for (vpiHandle item : kItems) {
      vpiHandle body = vpi_handle(vpiStmt, item);
      ASSERT_NE(body, nullptr) << kWhere;
      EXPECT_EQ(vpi_get(vpiType, body), vpiAssignment) << kWhere;
    }
  }
}

}  // namespace
}  // namespace delta
