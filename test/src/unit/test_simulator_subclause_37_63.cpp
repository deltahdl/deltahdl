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

// §37.63 Process: the object model diagram draws process (with its initial,
// final, and always members) traversing to and from module and stmt, and gives
// the process class one property access edge - "-> always type", int:
// vpiAlwaysType. The module<->process, process<->stmt, and stmt->scope edges
// are the generic one-to-one/one-to-many traversals already provided by the
// data model; the clause's only numbered Detail governs the property edge.
// Detail 1 restricts vpiAlwaysType to exactly four constants. These tests
// observe the production code apply that restriction (the VpiIsAlwaysType
// guard) through the public vpi_get(vpiAlwaysType) dispatch path - both the
// legal values it admits and the values it rejects to vpiUndefined.

// The fixture installs a context so the public vpi_get entry point runs its
// real dispatch over the test objects.
class Process : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D1 applied through the public dispatch: a process carrying one of the four
// always types reports exactly that constant through vpi_get(vpiAlwaysType).
// Driving all four legal constants here also exercises the admitting branch of
// the VpiIsAlwaysType guard, since a value the guard rejected would come back
// as vpiUndefined rather than the constant.
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

// D1 applied through the public dispatch: a process with no legal always type
// reports vpiUndefined rather than handing back a value outside the four. This
// is the outcome that distinguishes the clause's restriction, applied by the
// production guard, from simply returning the stored field - covering both an
// unset always_type (an initial or final process) and a stored value that is
// not one of the four.
TEST_F(Process, ProcessWithoutALegalAlwaysTypeReportsUndefined) {
  VpiObject initial_process;
  initial_process.type = vpiInitial;  // not an always procedure; always_type 0
  EXPECT_EQ(vpi_get(vpiAlwaysType, VpiHandleOf(&initial_process)),
            vpiUndefined);

  VpiObject bad_process;
  bad_process.type = vpiAlways;
  bad_process.always_type = vpiInitial;  // a value outside the four
  EXPECT_EQ(vpi_get(vpiAlwaysType, VpiHandleOf(&bad_process)), vpiUndefined);
}

// -----------------------------------------------------------------------------
// The edge between a process and the statement it executes. §37.63 draws it
// with a head at each end: the statement end is the `stmt` class, which §37.60
// fills with the scope and atomic statement kinds, and the process end is the
// `process` class of the initial, final and always procedures. §37.4.1 makes
// each enclosure a grouping rather than an object, so vpiStmt and vpiProcess
// are the two groups' names; matching either against an object's own type,
// which is what the generic traversal does, reached the body of no procedure
// any design elaborates and let no statement name the procedure running it.
// -----------------------------------------------------------------------------

// §37.63 (figure, process -> stmt): an always procedure reaches the statement
// it executes, whichever of the kinds the `stmt` class groups that statement
// is - here the begin block a multi-statement body is written as.
TEST_F(Process, AProcessReachesTheStatementItExecutes) {
  VpiObject body;
  body.type = vpiNamedBegin;

  VpiObject process;
  process.type = vpiAlways;
  process.children = {&body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&process))), &body);
}

// §37.63 (figure): the same edge is drawn on all three procedure kinds, and a
// body written as a single atomic statement is as much a member of the `stmt`
// class as a block is.
TEST_F(Process, AnInitialReachesAnAtomicStatementBody) {
  VpiObject body;
  body.type = vpiAssignment;

  VpiObject process;
  process.type = vpiInitial;
  process.children = {&body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&process))), &body);
}

// §37.63 (figure, stmt -> process): the arrow carries a head at each end, so a
// statement names the procedure running it. A statement nested inside the
// procedure's block reaches the same procedure, the edge being drawn to the
// process rather than to the immediately enclosing statement.
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

// §37.63 (figure): a statement standing under no procedure names none, rather
// than some enclosing object of another kind.
TEST_F(Process, AStatementOutsideAProcedureReachesNone) {
  VpiObject mod;
  mod.type = kVpiModule;

  VpiObject stmt;
  stmt.type = vpiAssignment;
  stmt.parent = &mod;
  mod.children = {&stmt};

  EXPECT_EQ(vpi_handle(vpiProcess, VpiHandleOf(&stmt)), nullptr);
}

// -----------------------------------------------------------------------------
// The procedures of a run, built from the elaborated design rather than by
// hand.
// -----------------------------------------------------------------------------

class ProcessesOfARun : public VpiDesignRun {
 protected:
  // The first procedure `scope` holds, null for none.
  static vpiHandle FirstProcess(vpiHandle scope) {
    vpiHandle it = vpi_iterate(vpiProcess, scope);
    return it == nullptr ? nullptr : vpi_scan(it);
  }
};

// §37.63 (figure, module -> process): a module reaches each procedure it
// declares, in the order written, as an object of its own kind.
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

// §37.63 (figure, process -> module): a procedure reaches back its module.
TEST_F(ProcessesOfARun, AProcedureReachesItsModule) {
  Run("module top; logic a; initial a = 0; endmodule\n");
  vpiHandle proc = FirstProcess(By("top"));
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModule, proc)), VpiObjectOf(By("top")));
}

// A submodule's procedures are its own, not the module instantiating it.
TEST_F(ProcessesOfARun, ASubmodulesProceduresAreItsOwn) {
  Run("module sub; logic a; initial a = 0; endmodule\n"
      "module top; sub u(); endmodule\n");
  EXPECT_EQ(KindsOf(vpiProcess, By("top")), std::vector<int>{});
  EXPECT_EQ(KindsOf(vpiProcess, By("top.u")), std::vector<int>{vpiInitial});
}

// A concurrent assertion the elaborator runs as a process is no procedure the
// source wrote.
TEST_F(ProcessesOfARun, AnAssertionIsNoProcedure) {
  Run("module top; logic a, c;\n"
      "  assert property (@(posedge c) a);\n"
      "  initial a = 0;\n"
      "endmodule\n");
  EXPECT_EQ(KindsOf(vpiProcess, By("top")), std::vector<int>{vpiInitial});
}

// D1: an always procedure reports the keyword that opened it, and an initial
// reports no always type.
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

// §37.63 (figure, process <-> stmt): a procedure whose body is a named block
// reaches the block, which reaches back the procedure, and the block is still
// named under the module and one of its scopes.
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

// A block nested in the body runs in the same procedure.
TEST_F(ProcessesOfARun, ANestedBlockReachesTheProcedureRunningIt) {
  Run("module top; initial begin : outer begin : inner end end endmodule\n");
  vpiHandle proc = FirstProcess(By("top"));
  ASSERT_NE(proc, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, By("top.outer.inner"))),
            VpiObjectOf(proc));
}

// A body written as a plain begin is a begin of the run, though no scope
// (§37.12 detail 1), which the procedure reaches and runs; a named block
// inside it runs in the procedure too (#5060).
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

// A procedure whose body is an event statement reaches it, both ways.
TEST_F(ProcessesOfARun, AProcedureReachesItsEventStatementBody) {
  Run("module top; event e; initial -> e; endmodule\n");
  vpiHandle proc = FirstProcess(By("top"));
  ASSERT_NE(proc, nullptr);
  vpiHandle body = vpi_handle(vpiStmt, proc);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiEventStmt);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, body)), VpiObjectOf(proc));
}

// §37.62 with §37.12: an event statement written inside a named block hangs
// from the block, which is the scope it stands in.
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

}  // namespace
}  // namespace delta
