#include <gtest/gtest.h>

#include <vector>

#include "helpers_event_callbacks.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// The first statement of `type` within `stmt`, searched through the
// statements it holds, depth first; null for none.
vpiHandle FirstStmtOf(int type, vpiHandle stmt) {
  if (stmt == nullptr) return nullptr;
  if (vpi_get(vpiType, stmt) == type) return stmt;
  if (vpiHandle found = FirstStmtOf(type, vpi_handle(vpiStmt, stmt))) {
    return found;
  }
  vpiHandle it = vpi_iterate(vpiStmt, stmt);
  if (it == nullptr) return nullptr;
  while (vpiHandle child = vpi_scan(it)) {
    if (vpiHandle found = FirstStmtOf(type, child)) {
      vpi_release_handle(it);
      return found;
    }
  }
  return nullptr;
}

// The first statement of `type` in a process of `top`.
vpiHandle FirstStmtOfTop(int type) {
  vpiHandle it = vpi_iterate(vpiProcess, TopObject("top"));
  if (it == nullptr) return nullptr;
  while (vpiHandle proc = vpi_scan(it)) {
    if (vpiHandle found = FirstStmtOf(type, vpi_handle(vpiStmt, proc))) {
      vpi_release_handle(it);
      return found;
    }
  }
  return nullptr;
}

// §38.36.1: a cbValueChange placed on an event statement is called each time
// the statement executes, with no value (#7478).
TEST_F(EventCallbacksOfARun, AValueChangeOnAnEventStatementFiresAsItRuns) {
  Armer() = [] {
    PlaceEventCallback(cbValueChange, FirstStmtOfTop(vpiEventStmt));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; event ev;\n"
      "  initial begin $arm; repeat (2) begin #1 -> ev; end end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kChanges = DeliveriesOf(cbValueChange);
  ASSERT_EQ(kChanges.size(), 2u);
  EXPECT_EQ(kChanges[0].obj_type, vpiEventStmt);
  EXPECT_FALSE(kChanges[0].has_value);
  EXPECT_EQ(kChanges[0].now, 1u);
  EXPECT_FALSE(kChanges[1].has_value);
  EXPECT_EQ(kChanges[1].now, 2u);
}

// §38.36.1: a cbValueChange registered in vpiStrengthVal is called when the
// net's strength alone changes, and one in any other format is not (#7479).
TEST_F(EventCallbacksOfARun, AStrengthOnlyChangeFiresOnlyAStrengthCallback) {
  Armer() = [] {
    PlaceEventCallback(cbValueChange, TopObject("top.w"), vpiStrengthVal);
    PlaceEventCallback(cbValueChange, TopObject("top.w"), vpiBinStrVal);
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  reg en = 1;\n"
      "  wire w;\n"
      "  assign (strong1, strong0) w = en ? 1'b1 : 1'bz;\n"
      "  assign (weak1, weak0) w = 1'b1;\n"
      "  initial $arm;\n"
      "  initial #1 en = 0;\n"
      "endmodule\n");
  int strength_calls = 0;
  int text_calls = 0;
  for (const EventDelivery& d : DeliveriesOf(cbValueChange)) {
    if (d.now != 1) continue;
    if (d.format == vpiStrengthVal) ++strength_calls;
    if (d.format == vpiBinStrVal) ++text_calls;
  }
  EXPECT_EQ(strength_calls, 1);
  EXPECT_EQ(text_calls, 0);
}

constexpr const char* kForceReleaseOfA =
    "module top; timeunit 1ns; timeprecision 1ns; logic [3:0] a = 0;\n"
    "  initial begin $arm; #1 force a = 4'd9; #1 release a; end\n"
    "endmodule\n";

// §38.36.1: a cbForce or cbRelease placed on no object is given the value of
// the forced or released object after the statement (#7480).
TEST_F(EventCallbacksOfARun, AForceCallbackOnNoObjectIsGivenTheValue) {
  Armer() = [] {
    PlaceEventCallback(cbForce, nullptr);
    PlaceEventCallback(cbRelease, nullptr);
  };
  Run(kForceReleaseOfA);
  const std::vector<EventDelivery> kForces = DeliveriesOf(cbForce);
  ASSERT_EQ(kForces.size(), 1u);
  EXPECT_EQ(kForces[0].value, 9);
  const std::vector<EventDelivery> kReleases = DeliveriesOf(cbRelease);
  ASSERT_EQ(kReleases.size(), 1u);
  EXPECT_EQ(kReleases[0].value, 9);
  EXPECT_EQ(kReleases[0].now, 2u);
}

// §38.36.1: cbAssign is called after a procedural assign and cbDeassign after
// a deassign, each given the statement and the target's value (#7481).
TEST_F(EventCallbacksOfARun, AssignAndDeassignCallbacksFire) {
  Armer() = [] {
    PlaceEventCallback(cbAssign, TopObject("top.q"));
    PlaceEventCallback(cbDeassign, TopObject("top.q"));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; reg q;\n"
      "  initial begin $arm; #1 assign q = 1'b1; #1 deassign q; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kAssigns = DeliveriesOf(cbAssign);
  ASSERT_EQ(kAssigns.size(), 1u);
  EXPECT_EQ(kAssigns[0].obj_type, vpiAssignStmt);
  EXPECT_EQ(kAssigns[0].value, 1);
  EXPECT_EQ(kAssigns[0].now, 1u);
  const std::vector<EventDelivery> kDeassigns = DeliveriesOf(cbDeassign);
  ASSERT_EQ(kDeassigns.size(), 1u);
  EXPECT_EQ(kDeassigns[0].obj_type, vpiDeassign);
  EXPECT_EQ(kDeassigns[0].value, 1);
  EXPECT_EQ(kDeassigns[0].now, 2u);
}

// §38.36.1: cbEnterThread is called each time a thread resumes execution,
// given the thread (#7482).
TEST_F(EventCallbacksOfARun, AnEnterThreadCallbackFiresOnEachResume) {
  Armer() = [] { PlaceEventCallback(cbEnterThread, nullptr); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  initial begin $arm; #1; #1; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kEntries = DeliveriesOf(cbEnterThread);
  ASSERT_EQ(kEntries.size(), 2u);
  EXPECT_EQ(kEntries[0].obj_type, vpiThread);
  EXPECT_EQ(kEntries[0].now, 1u);
  EXPECT_EQ(kEntries[1].obj_type, vpiThread);
  EXPECT_EQ(kEntries[1].now, 2u);
}

}  // namespace
}  // namespace delta
