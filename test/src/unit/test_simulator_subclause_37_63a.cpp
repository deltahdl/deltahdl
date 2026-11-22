#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Process : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Process, ProcessReportsItsAlwaysTypeThroughVpiGet) {
  for (int always_type :
       {vpiAlways, vpiAlwaysComb, vpiAlwaysFF, vpiAlwaysLatch}) {
    VpiObject process;
    process.type = vpiAlways;
    process.always_type = always_type;
    EXPECT_EQ(vpi_get(vpiAlwaysType, VpiHandleOf(&process)), always_type)
        << "always_type constant " << always_type;
  }
}

TEST_F(Process, ProcessWithoutALegalAlwaysTypeReportsUndefined) {
  VpiObject initial_process;
  initial_process.type = vpiInitial;
  EXPECT_EQ(vpi_get(vpiAlwaysType, VpiHandleOf(&initial_process)),
            vpiUndefined);

  VpiObject bad_process;
  bad_process.type = vpiAlways;
  bad_process.always_type = vpiInitial;
  EXPECT_EQ(vpi_get(vpiAlwaysType, VpiHandleOf(&bad_process)), vpiUndefined);
}

TEST_F(Process, AProcessReachesTheStatementItExecutes) {
  VpiObject body;
  body.type = vpiNamedBegin;

  VpiObject process;
  process.type = vpiAlways;
  process.children = {&body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&process))), &body);
}

TEST_F(Process, AnInitialReachesAnAtomicStatementBody) {
  VpiObject body;
  body.type = vpiAssignment;

  VpiObject process;
  process.type = vpiInitial;
  process.children = {&body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&process))), &body);
}

TEST_F(Process, AStatementReachesTheProcedureRunningIt) {
  VpiObject process;
  process.type = vpiFinal;

  VpiObject body;
  body.type = vpiBegin;
  body.parent = &process;
  process.children = {&body};

  VpiObject nested;
  nested.type = vpiAssignment;
  nested.parent = &body;
  body.children = {&nested};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, VpiHandleOf(&body))), &process);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, VpiHandleOf(&nested))),
            &process);
}

TEST_F(Process, AStatementOutsideAProcedureReachesNone) {
  VpiObject mod;
  mod.type = kVpiModule;

  VpiObject stmt;
  stmt.type = vpiAssignment;
  stmt.parent = &mod;
  mod.children = {&stmt};

  EXPECT_EQ(vpi_handle(vpiProcess, VpiHandleOf(&stmt)), nullptr);
}

class ProcessesOfARun : public VpiDesignRun {
 protected:
  static vpiHandle FirstProcess(vpiHandle scope) {
    vpiHandle it = vpi_iterate(vpiProcess, scope);
    return it == nullptr ? nullptr : vpi_scan(it);
  }
};

TEST_F(ProcessesOfARun, AModuleIteratesItsProcedures) {
  Run("module top; logic a, c;\n"
      "  initial a = 0;\n"
      "  always @(posedge c) a <= ~a;\n"
      "  final a = 1;\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(KindsOf(vpiProcess, top),
            (std::vector<int>{vpiInitial, vpiAlways, vpiFinal}));
}

TEST_F(ProcessesOfARun, AProcedureReachesItsModule) {
  Run("module top; logic a; initial a = 0; endmodule\n");
  vpiHandle proc = FirstProcess(By("top"));
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, proc)), VpiObjectOf(By("top")));
}

TEST_F(ProcessesOfARun, ASubmodulesProceduresAreItsOwn) {
  Run("module sub; logic a; initial a = 0; endmodule\n"
      "module top; sub u(); endmodule\n");
  EXPECT_EQ(KindsOf(vpiProcess, By("top")), std::vector<int>{});
  EXPECT_EQ(KindsOf(vpiProcess, By("top.u")), std::vector<int>{vpiInitial});
}

TEST_F(ProcessesOfARun, AnAssertionIsNoProcedure) {
  Run("module top; logic a, c;\n"
      "  assert property (@(posedge c) a);\n"
      "  initial a = 0;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiProcess, By("top")), std::vector<int>{vpiInitial});
}

TEST_F(ProcessesOfARun, AnAlwaysReportsTheKeywordThatOpenedIt) {
  Run("module top; logic a, b, c, d, e;\n"
      "  always @(posedge c) a <= 1;\n"
      "  always_comb b = c;\n"
      "  always_ff @(posedge c) d <= c;\n"
      "  always_latch if (c) e = c;\n"
      "  initial a = 0;\n"
      "endmodule\n");
  std::vector<int> always_types;
  vpiHandle it = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(it, nullptr);
  while (vpiHandle proc = vpi_scan(it)) {
    always_types.push_back(vpi_get(vpiAlwaysType, proc));
  }
  EXPECT_EQ(always_types,
            (std::vector<int>{vpiAlways, vpiAlwaysComb, vpiAlwaysFF,
                              vpiAlwaysLatch, vpiUndefined}));
}

TEST_F(ProcessesOfARun, AProcedureReachesItsNamedBlockBody) {
  Run("module top; initial begin : blk end endmodule\n");
  vpiHandle proc = FirstProcess(By("top"));
  vpiHandle blk = By("top.blk");
  ASSERT_NE(proc, nullptr);
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, proc)), VpiObjectOf(blk));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, blk)), VpiObjectOf(proc));
  EXPECT_EQ(NamesOf(vpiInternalScope, By("top")),
            std::vector<std::string>{"blk"});
}

TEST_F(ProcessesOfARun, ANestedBlockReachesTheProcedureRunningIt) {
  Run("module top; initial begin : outer begin : inner end end endmodule\n");
  vpiHandle proc = FirstProcess(By("top"));
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, By("top.outer.inner"))),
            VpiObjectOf(proc));
}

TEST_F(ProcessesOfARun, ABlockInsideAPlainBeginReachesItsProcedure) {
  Run("module top; initial begin begin : BLK end end endmodule\n");
  vpiHandle proc = FirstProcess(By("top"));
  ASSERT_NE(proc, nullptr);
  vpiHandle body = vpi_handle(vpiStmt, proc);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiBegin);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, body)), VpiObjectOf(proc));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, By("top.BLK"))),
            VpiObjectOf(proc));
}

TEST_F(ProcessesOfARun, AProcedureReachesItsEventStatementBody) {
  Run("module top; event e; initial -> e; endmodule\n");
  vpiHandle proc = FirstProcess(By("top"));
  ASSERT_NE(proc, nullptr);
  vpiHandle body = vpi_handle(vpiStmt, proc);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiEventStmt);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, body)), VpiObjectOf(proc));
}

TEST_F(ProcessesOfARun, AnEventStatementInsideANamedBlockHangsFromIt) {
  Run("module top; event e; initial begin : blk -> e; end endmodule\n");
  vpiHandle blk = By("top.blk");
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(KindsOf(vpiEventStmt, By("top")), std::vector<int>{});
  vpiHandle it = vpi_iterate(vpiEventStmt, blk);
  ASSERT_NE(it, nullptr);
  vpiHandle ev = vpi_scan(it);
  ASSERT_NE(ev, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, ev)), VpiObjectOf(blk));
  vpiHandle event = vpi_handle(vpiNamedEvent, ev);
  ASSERT_NE(event, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, event), "e");
}

TEST_F(ProcessesOfARun, AnAlwaysReachesTheControlItWasWrittenWith) {
  Run("module top; bit c, d;\n"
      "  always #5 c = ~c;\n"
      "  always @* d = 1;\n"
      "  initial #12 $finish;\n"
      "endmodule\n");
  std::vector<int> bodies;
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  while (vpiHandle proc = vpi_scan(procs)) {
    vpiHandle body = vpi_handle(vpiStmt, proc);
    bodies.push_back(body == nullptr ? 0 : vpi_get(vpiType, body));
  }
  EXPECT_EQ(bodies, (std::vector<int>{vpiDelayControl, vpiEventControl,
                                      vpiDelayControl}));
}

}  // namespace
}  // namespace delta
