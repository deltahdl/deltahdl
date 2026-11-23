#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_annex_d_call_forms.h"
#include "helpers_event_callbacks.h"
#include "helpers_reported_error.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

TEST(OptionalScopeSim, InitialScopeIsFirstTopModule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.InteractiveScope(), "t");
}

TEST(OptionalScopeSim, ScopeAcceptsHierarchicalName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $scope(t.blk);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.blk");
}

TEST(OptionalScopeSim, ScopeAcceptsMultiLevelHierarchicalName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      $scope(t.outer.inner);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.outer.inner");
}

TEST(OptionalScopeSim, LastScopeWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin : blk\n"
      "    $scope(t);\n"
      "    $scope(t.blk);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.blk");
}

TEST(OptionalScopeSim, ScopeAcceptsAnInstanceATaskAndAFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module sub;\n"
      "  function int f; return 1; endfunction\n"
      "endmodule\n"
      "module t;\n"
      "  sub u1();\n"
      "  task tk; endtask\n"
      "  initial begin\n"
      "    $scope(t.u1);\n"
      "    $scope(t.tk);\n"
      "    $scope(t.u1.f);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.u1.f");
}

TEST(OptionalScopeSim, ScopeAcceptsANamedFork) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial fork : fk\n"
      "    $scope(t.fk);\n"
      "  join\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.fk");
}

TEST(OptionalScopeSim, ScopeAcceptsTheBeginALabelOpensAroundAStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    lbl: x = 1;\n"
      "    $scope(t.lbl);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.lbl");
}

TEST(OptionalScopeSim, ScopeAcceptsTheBlockALabelNamesOnAForeachLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a[2];\n"
      "  initial begin\n"
      "    lp: foreach (a[i]) a[i] = i;\n"
      "    $scope(t.lp);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.InteractiveScope(), "t.lp");
}

TEST(OptionalScopeSim, AConcurrentAssertionItemsLabelNamesNoScope) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0, x = 1;\n"
      "  a1: assert property (@(posedge clk) x);\n"
      "  initial $scope(t.a1);\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$scope takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.a1' is none",
                            4, "D.11"));
  EXPECT_EQ(f.ctx.InteractiveScope(), "t");
}

TEST(OptionalScopeSim, AnArgumentNamingNoScopeIsRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    $scope(t.nope);\n"
      "    $scope(t.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$scope takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.nope' is none",
                            4, "D.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$scope takes the complete hierarchical name of a "
                            "module, task, function, or named block, and "
                            "'t.v' is none",
                            5, "D.11"));
  EXPECT_EQ(f.ctx.InteractiveScope(), "t");
}

TEST_F(EventCallbacksOfARun, ScopeOnALabelledAssertionNotesItsBegin) {
  Armer() = [] { PlaceEventCallback(cbInteractiveScopeChange, nullptr); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic clk = 0, x = 1;\n"
      "  always @(posedge clk) begin\n"
      "    i1: assert (x) else begin end\n"
      "  end\n"
      "  initial begin $arm; #1 $scope(top.i1); end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kChanges =
      DeliveriesOf(cbInteractiveScopeChange);
  ASSERT_EQ(kChanges.size(), 1u);
  EXPECT_EQ(kChanges[0].obj_type, vpiNamedBegin);
  EXPECT_EQ(kChanges[0].obj, "i1");
}

std::string ScopeAfterRun(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  return f.ctx.InteractiveScope();
}

std::string NoneOfTheKinds(const std::string& arg) {
  std::string message =
      "$scope takes the complete hierarchical name of a module, task, "
      "function, or named block, and '";
  message += arg;
  message += "' is none";
  return message;
}

TEST(OptionalScopeSim, DISABLED_ManyTopsStartAtTheFirstTop) {
  SimFixture f;
  EXPECT_EQ(ScopeAfterRun("module b;\n  initial begin end\nendmodule\n"
                          "module a;\n  initial begin end\nendmodule\n",
                          f),
            "b");
}

TEST(OptionalScopeSim, AModuleDeclaredBeforeTheTopIsNotTheStart) {
  SimFixture f;
  EXPECT_EQ(ScopeAfterRun("module sub;\n  initial begin end\nendmodule\n"
                          "module t;\n  sub u1();\nendmodule\n",
                          f),
            "t");
}

TEST(OptionalScopeSim, TheTopModuleNameReturnsTheScopeToIt) {
  SimFixture f;
  EXPECT_EQ(ScopeAfterRun("module t;\n"
                          "  initial begin : blk\n"
                          "    $scope(t.blk);\n"
                          "    $scope(t);\n"
                          "  end\n"
                          "endmodule\n",
                          f),
            "t");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OptionalScopeSim, ATaskNameMakesTheTaskTheScope) {
  SimFixture f;
  EXPECT_EQ(ScopeAfterRun("module t;\n"
                          "  task tk; endtask\n"
                          "  initial $scope(t.tk);\n"
                          "endmodule\n",
                          f),
            "t.tk");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(OptionalScopeSim, ACallInATaskFunctionOrInstanceSetsTheScope) {
  struct Caller {
    const char* leaf_body;
    const char* top_body;
  };
  const Caller kCallers[] = {
      {"", "  task automatic tk; $scope(t.u1); endtask\n  initial tk();\n"},
      {"",
       "  function automatic void fn; $scope(t.u1); endfunction\n"
       "  initial fn();\n"},
      {"  initial $scope(t.u1);\n", ""},
  };
  for (const auto& caller : kCallers) {
    std::string src = "module sub;\nendmodule\nmodule leaf;\n";
    src += caller.leaf_body;
    src += "endmodule\nmodule t;\n  sub u1();\n  leaf l1();\n";
    src += caller.top_body;
    src += "endmodule\n";
    SimFixture f;
    EXPECT_EQ(ScopeAfterRun(src, f), "t.u1") << src;
    EXPECT_FALSE(f.diag.HasErrors()) << src;
  }
}

TEST(OptionalScopeSim, AnIncompleteNameIsRejectedBesideTheCompleteOne) {
  SimFixture f;
  EXPECT_EQ(ScopeAfterRun("module t;\n"
                          "  initial begin : blk\n"
                          "    $scope(t.blk);\n"
                          "    $scope(blk);\n"
                          "  end\n"
                          "endmodule\n",
                          f),
            "t.blk");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), NoneOfTheKinds("blk"), 4, "D.11"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), NoneOfTheKinds("t.blk"), 3, "D.11"));
}

TEST(OptionalScopeSim, AStringArgumentIsRejected) {
  SimFixture f;
  EXPECT_EQ(ScopeAfterRun("module t;\n"
                          "  initial $scope(\"t\");\n"
                          "endmodule\n",
                          f),
            "t");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), NoneOfTheKinds("\"t\""), 2, "D.11"));
}

TEST(OptionalScopeSim, AGenerateBlockIsRejected) {
  SimFixture f;
  EXPECT_EQ(ScopeAfterRun("module t;\n"
                          "  if (1) begin : g\n"
                          "    int gv;\n"
                          "  end\n"
                          "  initial $scope(t.g);\n"
                          "endmodule\n",
                          f),
            "t");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), NoneOfTheKinds("t.g"), 5, "D.11"));
}

void ExpectScopeOfNoAllowedKindRejected(const std::string& decls,
                                        const std::string& instance,
                                        const std::string& arg) {
  std::string src = decls;
  src += "module sub;\nendmodule\nmodule t;\n  sub s1();\n";
  src += instance;
  src += "  initial begin\n    $scope(t.s1);\n    $scope(";
  src += arg;
  src += ");\n  end\nendmodule\n";
  SimFixture f;
  EXPECT_EQ(ScopeAfterRun(src, f), "t.s1") << src;
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NoneOfTheKinds(arg),
                            LineHolding(src, "$scope(" + arg + ")"), "D.11"))
      << src;
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), NoneOfTheKinds("t.s1"),
                             LineHolding(src, "$scope(t.s1)"), "D.11"))
      << src;
}

TEST(OptionalScopeSim, DISABLED_AnInterfaceInstanceIsRejected) {
  ExpectScopeOfNoAllowedKindRejected(
      "interface ifc;\n  int iv;\nendinterface\n", "  ifc u();\n", "t.u");
}

TEST(OptionalScopeSim, AProgramIsRejected) {
  ExpectScopeOfNoAllowedKindRejected(
      "program p;\n  initial begin end\nendprogram\n", "", "p");
}

TEST(OptionalScopeSim, DISABLED_ACheckerInstanceIsRejected) {
  ExpectScopeOfNoAllowedKindRejected("checker chk;\nendchecker\n",
                                     "  chk c1();\n", "t.c1");
}

constexpr const char* kScopeForm =
    "$scope is written as a task statement with one hierarchical name, and "
    "this call is not";

TEST(OptionalScopeForm, DISABLED_NoArgumentListIsReported) {
  ExpectOnlyTheMalformedCallReported("$scope(t)", "$scope", kScopeForm, "D.11");
}

TEST(OptionalScopeForm, DISABLED_AnEmptyArgumentListIsReported) {
  ExpectOnlyTheMalformedCallReported("$scope(t)", "$scope()", kScopeForm,
                                     "D.11");
}

TEST(OptionalScopeForm, DISABLED_TwoArgumentsAreReported) {
  ExpectOnlyTheMalformedCallReported("$scope(t)", "$scope(t, t)", kScopeForm,
                                     "D.11");
}

}  // namespace
