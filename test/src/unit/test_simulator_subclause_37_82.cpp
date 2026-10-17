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

// §37.82 Active time format: the object model diagram carries a single edge
// from a circle, which §37.4.3 makes vpi_handle(vpiActiveTimeFormat, NULL),
// reaching §37.42's dotted `tf call` enclosure - so what it reaches is an
// object of one of the kinds that class groups, here the system task call
// $timeformat() that established the active time format. There is no BNF and no
// 'shall' BNF production, only one numbered detail:
//   1) if $timeformat() has not been called, vpi_handle(vpiActiveTimeFormat,
//      NULL) shall return NULL.
//
// Nothing stood that call object up. The run applied a $timeformat as the task
// executed and left the relation with nothing to reach, so every run answered
// the traversal the way detail 1 has only a run that never called the task
// answer it, and the edge this clause is reached nothing a design could
// produce. These tests drive the production dispatch through the public
// vpi_handle entry point, both on a context of their own and on a design that
// runs the task.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch, and holds two $timeformat calls for the run to note, neither
// of them a statement of a model the context holds.
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

// Detail 1: with no $timeformat() call recorded - the state of a fresh context
// - vpi_handle(vpiActiveTimeFormat, NULL) returns NULL rather than reaching any
// object.
TEST_F(ActiveTimeFormat, ReturnsNullWhenTimeformatNotCalled) {
  EXPECT_EQ(vpi_handle(vpiActiveTimeFormat, nullptr), nullptr);
}

// Diagram edge: once a $timeformat() call has set the active time format,
// vpi_handle(vpiActiveTimeFormat, NULL) reaches that call - an object of a kind
// §37.42's `tf call` class groups. With no model statement for the call, it is
// one of its own, which §37.60 detail 1 leaves unnamed as it does every system
// task's call statement without a label.
TEST_F(ActiveTimeFormat, ReachesTheTimeformatCallThatSetTheFormat) {
  ctx_.NoteTimeFormatCall(&first_, f_.ctx);

  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_get(vpiType, reached), vpiSysTaskCall);
  EXPECT_EQ(vpi_get_str(vpiName, reached), nullptr);
}

// §20.4.3 has a later $timeformat replace the configuration, so the call the
// active format came from is the later one and that is what the edge reaches.
TEST_F(ActiveTimeFormat, ReachesTheLatestCallWhenTheTaskRunsAgain) {
  ctx_.NoteTimeFormatCall(&first_, f_.ctx);
  vpiHandle first = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(first, nullptr);

  ctx_.NoteTimeFormatCall(&second_, f_.ctx);
  vpiHandle second = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_NE(second, first);
}

// Diagram edge / detail 1 both spell the traversal with a NULL second argument:
// the active-time-format relation originates at a circle, which §37.4.3 makes
// the top-level reference. So even with a $timeformat() call on record, asking
// for vpiActiveTimeFormat relative to a concrete object must not reach that
// recorded call.
TEST_F(ActiveTimeFormat, DoesNotReachTheTimeformatCallFromANonNullReference) {
  ctx_.NoteTimeFormatCall(&first_, f_.ctx);
  vpiHandle recorded = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(recorded, nullptr);

  VpiObject some_object;
  some_object.type = vpiSysTaskCall;

  EXPECT_NE(vpi_handle(vpiActiveTimeFormat, VpiHandleOf(&some_object)),
            recorded);
}

// End to end: a design that calls $timeformat leaves the run with the call the
// edge reaches, and one that does not leaves detail 1's NULL. This is the pair
// the clause distinguishes, observed on the path a design actually takes rather
// than on a call object a test stood up itself.
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
  ASSERT_EQ(out, "   5.00 ns\n");  // the task ran and installed its format

  // A run that builds no VPI model has no statement for the call, so the call
  // it reaches is one of its own, standing for the call written (§37.42
  // detail 9) and unnamed (§37.60 detail 1).
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
  ASSERT_FALSE(out.empty());  // the design ran; it just never called the task

  EXPECT_EQ(vpi_handle(vpiActiveTimeFormat, nullptr), nullptr);

  SetGlobalVpiContext(nullptr);
}

// A run that builds its VPI model holds the statement making the call, and that
// statement is what the edge reaches, so the handle the edge gives and the one
// a walk of the design reaches are one object under §38.3.
class ActiveTimeFormatOfAModel : public VpiDesignRun {
 protected:
  // The statement of each process `scope` writes.
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

// §20.4.3 has the later call replace the format, so of two calls in the model
// the edge reaches the statement of the one that ran last.
TEST_F(ActiveTimeFormatOfAModel, TheEdgeReachesTheStatementOfTheLatestCall) {
  Run("module top;\n"
      "  initial $timeformat(-9, 2, \" ns\", 10);\n"
      "  initial #1 $timeformat(-6, 0, \" us\", 8);\n"
      "endmodule\n");
  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(vpi_get(vpiLineNo, reached), 3);
  // The second process's statement is its delay control, which the call it
  // delays stands under (§37.64).
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
