#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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
// real dispatch.
class ActiveTimeFormat : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Detail 1: with no $timeformat() call recorded - the state of a fresh context
// - vpi_handle(vpiActiveTimeFormat, NULL) returns NULL rather than reaching any
// object.
TEST_F(ActiveTimeFormat, ReturnsNullWhenTimeformatNotCalled) {
  EXPECT_EQ(vpi_handle(vpiActiveTimeFormat, nullptr), nullptr);
}

// Diagram edge: once a $timeformat() call has set the active time format,
// vpi_handle(vpiActiveTimeFormat, NULL) reaches that call - an object of a kind
// §37.42's `tf call` class groups, carrying the task's name.
TEST_F(ActiveTimeFormat, ReachesTheTimeformatCallThatSetTheFormat) {
  ctx_.NoteTimeFormatCall();

  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(reached->type, vpiSysTaskCall);
  EXPECT_EQ(reached->name, "$timeformat");
}

// §20.4.3 has a later $timeformat replace the configuration, so the call the
// active format came from is the later one and that is what the edge reaches.
TEST_F(ActiveTimeFormat, ReachesTheLatestCallWhenTheTaskRunsAgain) {
  ctx_.NoteTimeFormatCall();
  vpiHandle first = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(first, nullptr);

  ctx_.NoteTimeFormatCall();
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
  ctx_.NoteTimeFormatCall();
  vpiHandle recorded = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(recorded, nullptr);

  VpiObject some_object;
  some_object.type = vpiSysTaskCall;

  EXPECT_NE(vpi_handle(vpiActiveTimeFormat, &some_object), recorded);
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

  vpiHandle reached = vpi_handle(vpiActiveTimeFormat, nullptr);
  ASSERT_NE(reached, nullptr);
  EXPECT_EQ(reached->type, vpiSysTaskCall);
  EXPECT_EQ(reached->name, "$timeformat");

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

}  // namespace
}  // namespace delta
