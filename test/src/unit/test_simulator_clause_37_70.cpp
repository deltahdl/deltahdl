#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.70 Forever: the object model diagram draws a single, unlabeled edge from a
// forever statement to a body statement - the vpiStmt relation. The clause carries
// no numbered Details, no 'shall' sentences, and no properties; the body edge is
// its only content. Unlike the looping statements of §37.66, a forever statement
// has no controlling condition, so the diagram draws no vpiCondition edge. The body
// edge needs no dedicated production code: a forever statement is not one of the
// kinds that override vpiStmt (an event control, a delay control, or a task/func),
// so it is served by the generic vpiStmt traversal in VpiHandleC. These tests
// observe that production path applying the rule to a forever object.

// The fixture installs a context so the public VpiHandleC entry point runs its real
// dispatch over the test objects.
class Forever : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Body edge (the diagram's lone unlabeled arrow to a statement): a forever
// statement reaches its body through the public vpi_handle(vpiStmt, ...) dispatch
// path, which resolves to the generic vpiStmt traversal.
TEST_F(Forever, ForeverStatementReachesBodyThroughVpiStmt) {
  VpiObject body;
  body.type = vpiStmt;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&body};

  EXPECT_EQ(VpiHandleC(vpiStmt, &forever_stmt), &body);
}

// Body edge is type-directed: when the forever object also carries an incidental
// non-statement child, the vpiStmt relation skips it and returns the body
// statement rather than the first child.
TEST_F(Forever, ForeverBodyFoundAmongOtherChildren) {
  VpiObject other;
  other.type = vpiOperation;  // a non-statement child, listed first

  VpiObject body;
  body.type = vpiStmt;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&other, &body};

  EXPECT_EQ(VpiHandleC(vpiStmt, &forever_stmt), &body);
}

// Body edge reports no statement when the forever object has no statement child:
// the generic traversal finds nothing to return.
TEST_F(Forever, ForeverWithoutBodyReportsNoStatement) {
  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;

  EXPECT_EQ(VpiHandleC(vpiStmt, &forever_stmt), nullptr);
}

}  // namespace
}  // namespace delta
