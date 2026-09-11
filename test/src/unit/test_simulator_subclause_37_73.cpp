#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.73 Expect: the object model diagram draws three single arrows out of an
// expect statement - an untagged one to the property specification it watches,
// an untagged one to the dotted `stmt` enclosure for the action a passing
// property runs, and a vpiElseStmt one to a second statement, the action a
// failing property runs. §37.4.3 names an untagged arrow by putting "vpi" in
// front of the target enclosure's words, so the first two are vpiPropertySpec
// and vpiStmt. The clause carries no numbered Details, no 'shall' sentences and
// no properties; the three edges are its whole content.
//
// The property specification is drawn in a solid enclosure, so it is a kind of
// its own and a child carries it: the generic, type-directed walk serves that
// edge. The two actions are not. §37.4.1 makes a dotted enclosure a class
// grouping other objects and classes, so each action carries the kind a
// statement of a design carries - a begin, an assignment, a task call - and
// neither carries vpiStmt or vpiElseStmt, which name the arrows. Read the other
// way, as a child whose own type is the relation tag, neither action of any
// expect statement that could be written was reached: the pass action needed
// the body resolver the process, loop, wait, forever and conditional kinds
// share, and the fail action needed telling from it by position, as 16.17
// writes the two one after the other. These tests observe each edge through its
// public dispatch.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class Expect : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Property-spec edge (the arrow to the solid `property spec` enclosure): an
// expect statement reaches the specification it watches through
// vpi_handle(vpiPropertySpec, ...). The edge is type-directed, so an incidental
// non-spec child listed first is skipped and the specification is returned
// rather than the first child.
TEST_F(Expect, ExpectStatementReachesItsPropertySpecification) {
  VpiObject incidental;
  incidental.type = vpiOperation;  // a non-spec child, listed first

  VpiObject spec;
  spec.type = vpiPropertySpec;

  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;
  expect_stmt.children = {&incidental, &spec};

  EXPECT_EQ(vpi_handle(vpiPropertySpec, &expect_stmt), &spec);
}

// Pass and fail actions: an expect statement reaches the action a passing
// property runs through vpiStmt and the action a failing one runs through
// vpiElseStmt. Both carry the kinds the `stmt` class groups and are told apart
// by position, so the two relations reach different statements rather than
// handing the same one back twice.
TEST_F(Expect, PassAndFailActionsAreTheFirstAndSecondStatements) {
  VpiObject spec;
  spec.type = vpiPropertySpec;

  VpiObject pass;
  pass.type = vpiBegin;

  VpiObject fail;
  fail.type = vpiSysTaskCall;  // an $error call, as 16.17 writes one

  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;
  expect_stmt.children = {&spec, &pass, &fail};

  EXPECT_EQ(vpi_handle(vpiStmt, &expect_stmt), &pass);
  EXPECT_EQ(vpi_handle(vpiElseStmt, &expect_stmt), &fail);
}

// Both actions are reached whatever kind they are written as, including the
// case where they carry the same kind as each other - position, not kind, is
// what separates them.
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

    EXPECT_EQ(vpi_handle(vpiStmt, &expect_stmt), &pass)
        << "action kind " << action_kind;
    EXPECT_EQ(vpi_handle(vpiElseStmt, &expect_stmt), &fail)
        << "action kind " << action_kind;
  }
}

// An expect statement written with a pass action and no else reports no fail
// action, so the one statement it carries is not handed back for both edges.
TEST_F(Expect, FailActionIsNullWhenTheExpectStatementHasOnlyAPassAction) {
  VpiObject spec;
  spec.type = vpiPropertySpec;

  VpiObject pass;
  pass.type = vpiBegin;

  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;
  expect_stmt.children = {&spec, &pass};

  EXPECT_EQ(vpi_handle(vpiStmt, &expect_stmt), &pass);
  EXPECT_EQ(vpi_handle(vpiElseStmt, &expect_stmt), nullptr);
}

// Edge: each of the three relations reports no handle when the expect statement
// carries no matching child, and a non-statement child is not mistaken for an
// action by either statement relation.
TEST_F(Expect, ExpectStatementWithoutBodyReportsNullThroughEachRelation) {
  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;

  EXPECT_EQ(vpi_handle(vpiPropertySpec, &expect_stmt), nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, &expect_stmt), nullptr);
  EXPECT_EQ(vpi_handle(vpiElseStmt, &expect_stmt), nullptr);

  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject spec_only;
  spec_only.type = vpiExpectStmt;
  spec_only.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiStmt, &spec_only), nullptr);
  EXPECT_EQ(vpi_handle(vpiElseStmt, &spec_only), nullptr);
}

}  // namespace
}  // namespace delta
