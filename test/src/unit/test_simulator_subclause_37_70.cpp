#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.70 Forever: the object model diagram draws a single, unlabeled edge from
// a forever statement to the dotted `stmt` enclosure. §37.4.3 makes an untagged
// single arrow a vpi_handle() relation whose type is the enclosure's words with
// "vpi" in front, so the edge is vpiStmt and it is the whole of this clause:
// there are no numbered Details, no 'shall' sentences and no properties, and -
// unlike the looping statements of §37.66 - a forever carries no controlling
// condition.
//
// §37.4.1 makes a dotted enclosure a class that "groups other objects and
// classes" rather than a kind of its own, so the body a forever reaches carries
// the kind a statement of a design carries - an unnamed begin, an assignment, a
// nested forever - and never vpiStmt, which is the class's name. Read the other
// way, as a child whose own type is the relation tag, the relation reached the
// body of no forever loop that could be written. These tests observe the body
// resolver applying the class reading to a forever statement.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class Forever : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Body edge (the diagram's lone unlabeled arrow to `stmt`): a forever statement
// reaches the body it loops over through vpi_handle(vpiStmt, ...). The body
// here is an unnamed begin, which is one of the block kinds the `stmt` class
// groups and what a forever with more than one statement in it holds.
TEST_F(Forever, ForeverStatementReachesBodyByTheKindTheStmtClassGroups) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&body};

  EXPECT_EQ(vpi_handle(vpiStmt, &forever_stmt), &body);
}

// Body edge: the kinds the `stmt` class groups are reached whatever the body is
// written as. A forever whose body is a single statement holds that statement
// rather than a block, and a forever nested directly inside another is itself
// the outer one's body.
TEST_F(Forever, ForeverBodyIsReachedForEachKindAStatementCarries) {
  for (int body_kind : {vpiAssignment, vpiTaskCall, vpiNamedBegin, vpiFork,
                        vpiForever, vpiNullStmt}) {
    VpiObject body;
    body.type = body_kind;

    VpiObject forever_stmt;
    forever_stmt.type = vpiForever;
    forever_stmt.children = {&body};

    EXPECT_EQ(vpi_handle(vpiStmt, &forever_stmt), &body)
        << "body kind " << body_kind;
  }
}

// Body edge is type-directed: where the forever object also carries a
// non-statement child, the relation steps over it and returns the statement
// rather than the first child. An expression stands here for the child a
// forever does not draw - the clause gives it no condition edge at all.
TEST_F(Forever, ForeverBodyFoundAmongOtherChildren) {
  VpiObject other;
  other.type = vpiOperation;  // a non-statement child, listed first

  VpiObject body;
  body.type = vpiBegin;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&other, &body};

  EXPECT_EQ(vpi_handle(vpiStmt, &forever_stmt), &body);
}

// Body edge reports no statement when the forever object carries none: a
// forever with only a non-statement child yields null rather than handing that
// child back, and one with no children at all yields null too.
TEST_F(Forever, ForeverWithoutBodyReportsNoStatement) {
  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;

  EXPECT_EQ(vpi_handle(vpiStmt, &forever_stmt), nullptr);

  VpiObject other;
  other.type = vpiOperation;

  VpiObject forever_with_no_stmt;
  forever_with_no_stmt.type = vpiForever;
  forever_with_no_stmt.children = {&other};

  EXPECT_EQ(vpi_handle(vpiStmt, &forever_with_no_stmt), nullptr);
}

// The clause draws no other edge: a forever has no controlling condition, so
// asking one for vpiCondition reports nothing even where it carries an
// expression child that a loop of §37.66 would answer with.
TEST_F(Forever, ForeverDrawsNoConditionEdge) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject body;
  body.type = vpiBegin;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&expr, &body};

  EXPECT_EQ(vpi_handle(vpiCondition, &forever_stmt), nullptr);
  EXPECT_EQ(vpi_handle(vpiStmt, &forever_stmt), &body);
}

}  // namespace
}  // namespace delta
