#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

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

class ExpectFormsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("module top; logic clk, a; int i;\n"
        "  property p; @(posedge clk) a; endproperty\n"
        "  task t; endtask\n"
        "  initial expect (p) $display(\"p\");\n"
        "  initial expect (p);\n"
        "  initial expect (p) begin i = 1; end else i = 2;\n"
        "  initial expect (p) i = 1; else begin i = 2; end\n"
        "  initial expect (p) t(); else t();\n"
        "endmodule\n");
  }

  static vpiHandle ExpectAt(size_t n) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    return n < kProcs.size() ? vpi_handle(vpiStmt, kProcs[n]) : nullptr;
  }

  static int KindReached(int relation, size_t n) {
    vpiHandle expect = ExpectAt(n);
    vpiHandle action =
        expect == nullptr ? nullptr : vpi_handle(relation, expect);
    return action == nullptr ? 0 : vpi_get(vpiType, action);
  }
};

TEST_F(ExpectFormsOfARun, APassActionAloneIsTheStatementWithNoElse) {
  vpiHandle expect = ExpectAt(0);
  ASSERT_NE(expect, nullptr);
  EXPECT_EQ(vpi_get(vpiType, expect), vpiExpectStmt);
  EXPECT_EQ(ActionReached(vpiStmt, expect), "$display");
  EXPECT_EQ(vpi_handle(vpiElseStmt, expect), nullptr);
}

TEST_F(ExpectFormsOfARun, AnExpectWithNoActionReachesNeitherStatement) {
  vpiHandle expect = ExpectAt(1);
  ASSERT_NE(expect, nullptr);
  EXPECT_NE(vpi_handle(vpiPropertySpec, expect), nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, expect), nullptr);
  EXPECT_EQ(vpi_handle(vpiElseStmt, expect), nullptr);
}

TEST_F(ExpectFormsOfARun, EachActionIsReachedAsItsOwnKind) {
  EXPECT_EQ(KindReached(vpiStmt, 2), vpiBegin);
  EXPECT_EQ(KindReached(vpiElseStmt, 2), vpiAssignment);
  EXPECT_EQ(KindReached(vpiStmt, 3), vpiAssignment);
  EXPECT_EQ(KindReached(vpiElseStmt, 3), vpiBegin);
  EXPECT_EQ(KindReached(vpiStmt, 4), vpiTaskCall);
  EXPECT_EQ(KindReached(vpiElseStmt, 4), vpiTaskCall);
}

TEST_F(ExpectsOfARun, AnExpectClockedByTheDefaultClockingReachesItsSpec) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  initial expect (a) $display(\"p\");\n"
      "endmodule\n");
  const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
  ASSERT_EQ(kProcs.size(), 1U);
  vpiHandle expect = vpi_handle(vpiStmt, kProcs[0]);
  ASSERT_NE(expect, nullptr);
  EXPECT_EQ(vpi_get(vpiType, expect), vpiExpectStmt);
  vpiHandle spec = vpi_handle(vpiPropertySpec, expect);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

TEST_F(ExpectsOfARun, AnExpectInEachPlaceReachesItsSpecAndActions) {
  Run("package pk; logic clk, a;\n"
      "  task pt; expect (@(posedge clk) a) $display(\"p\"); else "
      "$write(\"f\");\n"
      "  endtask\n"
      "endpackage\n"
      "interface ifc; logic clk, a;\n"
      "  initial expect (@(posedge clk) a) $display(\"p\"); else "
      "$write(\"f\");\n"
      "endinterface\n"
      "program prg; logic clk, a;\n"
      "  initial expect (@(posedge clk) a) $display(\"p\"); else "
      "$write(\"f\");\n"
      "endprogram\n"
      "module top; logic clk, a; ifc i0(); prg p0();\n"
      "  class C; logic clk, a;\n"
      "    task ct; expect (@(posedge clk) a) $display(\"p\");\n"
      "      else $write(\"f\"); endtask\n"
      "  endclass\n"
      "  task tk; expect (@(posedge clk) a) $display(\"p\"); else "
      "$write(\"f\");\n"
      "  endtask\n"
      "endmodule\n");
  vpiHandle top = By("top");
  const std::vector<vpiHandle> kInterface = ObjectsOf(vpiProcess, By("top.i0"));
  const std::vector<vpiHandle> kProgram = ObjectsOf(vpiProcess, By("top.p0"));
  ASSERT_EQ(kInterface.size(), 1U);
  ASSERT_EQ(kProgram.size(), 1U);
  const std::vector<std::pair<const char*, vpiHandle>> kOwners{
      {"package task", Named(vpiTask, By("pk"), "pt")},
      {"interface initial", kInterface[0]},
      {"program initial", kProgram[0]},
      {"class method", Named(vpiMethods, Named(vpiClassDefn, top, "C"), "ct")},
      {"module task", Named(vpiTask, top, "tk")},
  };
  for (const auto& [where, owner] : kOwners) {
    ASSERT_NE(owner, nullptr) << where;
    vpiHandle expect = vpi_handle(vpiStmt, owner);
    ASSERT_NE(expect, nullptr) << where;
    EXPECT_EQ(vpi_get(vpiType, expect), vpiExpectStmt) << where;
    EXPECT_NE(vpi_handle(vpiPropertySpec, expect), nullptr) << where;
    EXPECT_EQ(ActionReached(vpiStmt, expect), "$display") << where;
    EXPECT_EQ(ActionReached(vpiElseStmt, expect), "$write") << where;
  }
}

}  // namespace
}  // namespace delta
