#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "parser/ast_expr.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ActiveTimeFormat : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    first_.kind = ExprKind::kSystemCall;
    first_.callee = "$timeformat";
    second_.kind = ExprKind::kSystemCall;
    second_.callee = "$timeformat";
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
  SimFixture f_;
  Expr first_;
  Expr second_;
};

TEST_F(ActiveTimeFormat, ReturnsNullWhenTimeformatNotCalled) {
  EXPECT_EQ(vpi_handle(vpiActiveTimeFormat, nullptr), nullptr);
}

TEST_F(ActiveTimeFormat, ReachesTheTimeformatCallThatSetTheFormat) {
  ctx_.NoteTimeFormatCall(&first_, f_.ctx);

  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_get(vpiType, reached), vpiSysTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, reached), nullptr);
}

TEST_F(ActiveTimeFormat, ReachesTheLatestCallWhenTheTaskRunsAgain) {
  ctx_.NoteTimeFormatCall(&first_, f_.ctx);
  vpiHandle first = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(first, nullptr);

  ctx_.NoteTimeFormatCall(&second_, f_.ctx);
  vpiHandle second = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_NE(second, first);
}

TEST_F(ActiveTimeFormat, DoesNotReachTheTimeformatCallFromANonNullReference) {
  ctx_.NoteTimeFormatCall(&first_, f_.ctx);
  vpiHandle recorded = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(recorded, nullptr);

  VpiObject some_object;
  some_object.type = vpiSysTaskCall;

  EXPECT_NE(vpi_handle(vpiActiveTimeFormat, VpiHandleOf(&some_object)),
            recorded);
}

TEST(ActiveTimeFormatSim, ADesignsTimeformatCallIsWhatTheEdgeReaches) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \" ns\", 10);\n"
      "    $display(\"%t\", 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_EQ(out, "   5.00 ns\n");

  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_get(vpiType, reached), vpiSysTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, reached), nullptr);
  EXPECT_STREQ(vpi_get_str(vpiDecompile, reached),
               "$timeformat(- 9, 2, \" ns\", 10)");

  SetGlobalVpiContext(nullptr);
}

TEST(ActiveTimeFormatSim, ADesignThatNeverCallsTheTaskReachesNothing) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%t\", 3);\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(out.empty());

  EXPECT_EQ(vpi_handle(vpiActiveTimeFormat, nullptr), nullptr);

  SetGlobalVpiContext(nullptr);
}

class ActiveTimeFormatOfAModel : public VpiDesignRun {
 protected:
  static std::vector<vpiHandle> BodiesOf(const std::string& scope) {
    std::vector<vpiHandle> bodies;
    for (vpiHandle process : ObjectsOf(vpiProcess, By(scope))) {
      bodies.push_back(vpi_handle(vpiStmt, process));
    }
    return bodies;
  }
};

TEST_F(ActiveTimeFormatOfAModel, TheEdgeReachesTheModelsCallStatement) {
  Run("module top;\n"
      "  initial $timeformat(-9, 2, \" ns\", 10);\n"
      "endmodule\n");
  const std::vector<vpiHandle> kBodies = BodiesOf("top");
  ASSERT_EQ(kBodies.size(), 1U);
  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_compare_objects(reached, kBodies[0]), 1);
  EXPECT_EQ(vpi_get_str(vpiName, reached), nullptr);
  EXPECT_EQ(vpi_get(vpiLineNo, reached), 2);
}

TEST_F(ActiveTimeFormatOfAModel, TheEdgeReachesTheStatementOfTheLatestCall) {
  Run("module top;\n"
      "  initial $timeformat(-9, 2, \" ns\", 10);\n"
      "  initial #1 $timeformat(-6, 0, \" us\", 8);\n"
      "endmodule\n");
  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_get(vpiLineNo, reached), 3);
  int matches = 0;
  for (vpiHandle body : BodiesOf("top")) {
    for (vpiHandle stmt : {body, vpi_handle(vpiStmt, body)}) {
      if (stmt != nullptr && vpi_compare_objects(reached, stmt) == 1) ++matches;
    }
  }
  EXPECT_EQ(matches, 1);
}

}  // namespace
}  // namespace delta
