#include <gtest/gtest.h>

#include <string>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Expect : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Expect, ExpectStatementReachesItsPropertySpecification) {
  VpiObject incidental;
  incidental.type = vpiOperation;

  VpiObject spec;
  spec.type = vpiPropertySpec;

  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;
  expect_stmt.children = {&incidental, &spec};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiPropertySpec, VpiHandleOf(&expect_stmt))),
            &spec);
}

TEST_F(Expect, PassAndFailActionsAreTheFirstAndSecondStatements) {
  VpiObject spec;
  spec.type = vpiPropertySpec;

  VpiObject pass;
  pass.type = vpiBegin;

  VpiObject fail;
  fail.type = vpiSysTaskCall;

  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;
  expect_stmt.children = {&spec, &pass, &fail};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&expect_stmt))), &pass);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiElseStmt, VpiHandleOf(&expect_stmt))),
            &fail);
}

TEST_F(Expect, EachKindAnActionCarriesIsReachedByItsOwnRelation) {
  for (int action_kind :
       {vpiAssignment, vpiNamedBegin, vpiFork, vpiIf, vpiNullStmt}) {
    VpiObject pass;
    pass.type = action_kind;

    VpiObject fail;
    fail.type = action_kind;

    VpiObject expect_stmt;
    expect_stmt.type = vpiExpectStmt;
    expect_stmt.children = {&pass, &fail};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&expect_stmt))),
              &pass)
        << "action kind " << action_kind;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiElseStmt, VpiHandleOf(&expect_stmt))),
              &fail)
        << "action kind " << action_kind;
  }
}

TEST_F(Expect, FailActionIsNullWhenTheExpectStatementHasOnlyAPassAction) {
  VpiObject spec;
  spec.type = vpiPropertySpec;

  VpiObject pass;
  pass.type = vpiBegin;

  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;
  expect_stmt.children = {&spec, &pass};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&expect_stmt))), &pass);
  EXPECT_EQ(vpi_handle(vpiElseStmt, VpiHandleOf(&expect_stmt)), nullptr);
}

TEST_F(Expect, ExpectStatementWithoutBodyReportsNullThroughEachRelation) {
  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;

  EXPECT_EQ(vpi_handle(vpiPropertySpec, VpiHandleOf(&expect_stmt)), nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&expect_stmt)), nullptr);
  EXPECT_EQ(vpi_handle(vpiElseStmt, VpiHandleOf(&expect_stmt)), nullptr);

  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject spec_only;
  spec_only.type = vpiExpectStmt;
  spec_only.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&spec_only)), nullptr);
  EXPECT_EQ(vpi_handle(vpiElseStmt, VpiHandleOf(&spec_only)), nullptr);
}

class ExpectsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle FirstHeldStatement() {
    vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
    if (procs == nullptr) return nullptr;
    vpiHandle block = vpi_handle(vpiStmt, vpi_scan(procs));
    vpiHandle held = block ? vpi_iterate(vpiStmt, block) : nullptr;
    return held ? vpi_scan(held) : nullptr;
  }

  static std::string NameReached(int relation, vpiHandle ref) {
    vpiHandle reached = vpi_handle(relation, ref);
    return reached == nullptr ? "" : vpi_get_str(vpiName, reached);
  }
};

TEST_F(ExpectsOfARun, AnExpectStatementReachesBothActions) {
  Run("module top; logic clk, a;\n"
      "  initial begin\n"
      "    expect (@(posedge clk) a) $display(\"p\"); else $write(\"f\");\n"
      "  end\n"
      "endmodule\n");
  vpiHandle expect = FirstHeldStatement();
  ASSERT_NE(expect, nullptr);
  EXPECT_EQ(vpi_get(vpiType, expect), vpiExpectStmt);
  EXPECT_EQ(ActionReached(vpiStmt, expect), "$display");
  EXPECT_EQ(ActionReached(vpiElseStmt, expect), "$write");
}

TEST_F(ExpectsOfARun, AFailActionAloneIsTheElseStatement) {
  Run("module top; logic clk, a;\n"
      "  initial begin\n"
      "    expect (@(posedge clk) a) else $write(\"f\");\n"
      "  end\n"
      "endmodule\n");
  vpiHandle expect = FirstHeldStatement();
  ASSERT_NE(expect, nullptr);
  EXPECT_EQ(ActionReached(vpiStmt, expect), "");
  EXPECT_EQ(ActionReached(vpiElseStmt, expect), "$write");
}

TEST_F(ExpectsOfARun, AnExpectStatementReachesItsPropertySpec) {
  Run("module top; logic clk, rst, a;\n"
      "  initial begin\n"
      "    expect (@(posedge clk) disable iff (rst) a);\n"
      "  end\n"
      "endmodule\n");
  vpiHandle expect = FirstHeldStatement();
  ASSERT_NE(expect, nullptr);
  vpiHandle spec = vpi_handle(vpiPropertySpec, expect);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, spec), vpiPropertySpec);
  EXPECT_EQ(NameReached(vpiDisableCondition, spec), "rst");
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
  EXPECT_NE(vpi_handle(vpiClockingEvent, spec), nullptr);
}

TEST_F(ExpectsOfARun, AnExpectOfADeclaredPropertyReachesAPropertySpec) {
  Run("module top; logic clk, a;\n"
      "  property p; @(posedge clk) a; endproperty\n"
      "  initial begin\n"
      "    expect (p) $display(\"p\");\n"
      "  end\n"
      "endmodule\n");
  vpiHandle expect = FirstHeldStatement();
  ASSERT_NE(expect, nullptr);
  vpiHandle spec = vpi_handle(vpiPropertySpec, expect);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, spec), vpiPropertySpec);
  vpiHandle instance = vpi_handle(vpiPropertyExpr, spec);
  ASSERT_NE(instance, nullptr);
  EXPECT_EQ(vpi_get(vpiType, instance), vpiPropertyInst);
}

TEST(ExpectModel, OnlyAnExpectStatementHasAnElse) {
  EXPECT_EQ(VpiExpectElseStmt(nullptr), nullptr);
  VpiObject wait;
  wait.type = vpiWait;
  EXPECT_EQ(VpiExpectElseStmt(&wait), nullptr);
}

}  // namespace
}  // namespace delta
