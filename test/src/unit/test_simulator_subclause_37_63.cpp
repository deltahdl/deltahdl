#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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
    EXPECT_EQ(vpi_get(vpiAlwaysType, &process), always_type)
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
  EXPECT_EQ(vpi_get(vpiAlwaysType, &initial_process), vpiUndefined);

  VpiObject bad_process;
  bad_process.type = vpiAlways;
  bad_process.always_type = vpiInitial;  // a value outside the four
  EXPECT_EQ(vpi_get(vpiAlwaysType, &bad_process), vpiUndefined);
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

  EXPECT_EQ(vpi_handle(vpiStmt, &process), &body);
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

  EXPECT_EQ(vpi_handle(vpiStmt, &process), &body);
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

  EXPECT_EQ(vpi_handle(vpiProcess, &body), &process);
  EXPECT_EQ(vpi_handle(vpiProcess, &nested), &process);
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

  EXPECT_EQ(vpi_handle(vpiProcess, &stmt), nullptr);
}

}  // namespace
}  // namespace delta
