#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.73 Expect: the object model diagram draws three edges out of an expect
// statement - a solid edge to the property specification it watches, an
// unlabeled edge to its pass action statement (vpiStmt), and a vpiElseStmt edge
// to its else (fail) action statement. The clause carries no numbered Details,
// no 'shall' sentences, and no properties; the three edges are its only content.
// None of the three needs dedicated production code. An expect statement is not
// one of the kinds that override vpiStmt (an event control, a delay control, or
// a task/func) and it is not the if-else kind that overrides vpiElseStmt, and no
// special case overrides vpiPropertySpec at all, so each edge is served by the
// generic, type-directed traversal in VpiHandleC: the relation tag names the
// kind of the child it returns. These tests observe that production path
// applying the rule to an expect statement object.

// The fixture installs a context so the public VpiHandleC entry point runs its
// real dispatch over the test objects.
class Expect : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Property-spec edge (the diagram's solid arrow): an expect statement reaches
// its property specification through vpi_handle(vpiPropertySpec, ...). The edge
// is type-directed, so an incidental non-spec child listed first is skipped and
// the property specification is returned rather than the first child.
TEST_F(Expect, ExpectStatementReachesItsPropertySpecification) {
  VpiObject incidental;
  incidental.type = vpiOperation;  // a non-spec child, listed first

  VpiObject spec;
  spec.type = vpiPropertySpec;

  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;
  expect_stmt.children = {&incidental, &spec};

  EXPECT_EQ(VpiHandleC(vpiPropertySpec, &expect_stmt), &spec);
}

// Pass- and else-statement edges (the two dashed arrows): an expect statement
// reaches its pass action through vpiStmt and its else action through
// vpiElseStmt. The two edges are routed to distinct children by relation tag -
// vpiStmt does not return the else child and vpiElseStmt does not return the
// pass child - which also shows that, unlike an if-else, an expect statement's
// vpiElseStmt edge is served by the generic traversal.
TEST_F(Expect, ExpectStatementReachesPassAndElseStatementsThroughDistinctRelations) {
  VpiObject pass;
  pass.type = vpiStmt;

  VpiObject els;
  els.type = vpiElseStmt;

  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;
  expect_stmt.children = {&pass, &els};

  EXPECT_EQ(VpiHandleC(vpiStmt, &expect_stmt), &pass);
  EXPECT_EQ(VpiHandleC(vpiElseStmt, &expect_stmt), &els);
}

// Edge: each of the three relations reports no handle when the expect statement
// carries no matching child - the generic traversal finds nothing to return.
TEST_F(Expect, ExpectStatementWithoutBodyReportsNullThroughEachRelation) {
  VpiObject expect_stmt;
  expect_stmt.type = vpiExpectStmt;

  EXPECT_EQ(VpiHandleC(vpiPropertySpec, &expect_stmt), nullptr);
  EXPECT_EQ(VpiHandleC(vpiStmt, &expect_stmt), nullptr);
  EXPECT_EQ(VpiHandleC(vpiElseStmt, &expect_stmt), nullptr);
}

}  // namespace
}  // namespace delta
