#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Forever : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Forever, ForeverStatementReachesBodyByTheKindTheStmtClassGroups) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&forever_stmt))),
            &body);
}

TEST_F(Forever, ForeverBodyIsReachedForEachKindAStatementCarries) {
  for (int body_kind : {vpiAssignment, vpiTaskCall, vpiNamedBegin, vpiFork,
                        vpiForever, vpiNullStmt}) {
    VpiObject body;
    body.type = body_kind;

    VpiObject forever_stmt;
    forever_stmt.type = vpiForever;
    forever_stmt.children = {&body};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&forever_stmt))),
              &body)
        << "body kind " << body_kind;
  }
}

TEST_F(Forever, ForeverBodyFoundAmongOtherChildren) {
  VpiObject other;
  other.type = vpiOperation;

  VpiObject body;
  body.type = vpiBegin;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&other, &body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&forever_stmt))),
            &body);
}

TEST_F(Forever, ForeverWithoutBodyReportsNoStatement) {
  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&forever_stmt)), nullptr);

  VpiObject other;
  other.type = vpiOperation;

  VpiObject forever_with_no_stmt;
  forever_with_no_stmt.type = vpiForever;
  forever_with_no_stmt.children = {&other};

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&forever_with_no_stmt)), nullptr);
}

TEST_F(Forever, ForeverDrawsNoConditionEdge) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject body;
  body.type = vpiBegin;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&expr, &body};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&forever_stmt)), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&forever_stmt))),
            &body);
}

class ForeverLoopsOfARun : public VpiDesignRun {};

TEST_F(ForeverLoopsOfARun, AForeverLoopIsAnObjectOfTheRun) {
  Run("module top; initial forever begin #1 $finish; end endmodule\n");
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  vpiHandle loop = vpi_handle(vpiStmt, vpi_scan(procs));
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiType, loop), vpiForever);
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiBegin);
  EXPECT_EQ(KindsOf(vpiStmt, body), std::vector<int>{vpiDelayControl});
}

}  // namespace
}  // namespace delta
