#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
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

// §38.36.1: a cbForce placed on a variable is called for a force of that
// variable and not for one of another: placed on b, it is called once, after
// b is forced to 5, and not after a is forced to 9.
TEST_F(EventCallbacksOfARun, AForceCallbackOnOneVariableSkipsAnother) {
  Armer() = [] { PlaceEventCallback(cbForce, TopObject("top.b")); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic [3:0] a = 0, b = 0;\n"
      "  initial begin $arm; #1 force a = 4'd9; #1 force b = 4'd5; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kForces = DeliveriesOf(cbForce);
  ASSERT_EQ(kForces.size(), 1u);
  EXPECT_EQ(kForces[0].value, 5);
  EXPECT_EQ(kForces[0].now, 2u);
}

// §38.36.1 with §38.36: a cbForce registered with no value structure is given
// none, one registered in vpiSuppressVal is given its structure unread, and
// one registered with no routine calls nothing.
TEST_F(EventCallbacksOfARun, AForceCallbackTakesTheValueItWasRegisteredFor) {
  Armer() = [] {
    s_cb_data data = {};
    data.reason = cbForce;
    data.cb_rtn = &RecordEventDelivery;
    ASSERT_NE(vpi_register_cb(&data), nullptr);
    data.cb_rtn = nullptr;
    ASSERT_NE(vpi_register_cb(&data), nullptr);
    PlaceEventCallback(cbForce, nullptr, vpiSuppressVal);
  };
  Run(kForceReleaseOfA);
  const std::vector<EventDelivery> kForces = DeliveriesOf(cbForce);
  ASSERT_EQ(kForces.size(), 2u);
  EXPECT_FALSE(kForces[0].has_value);
  EXPECT_TRUE(kForces[1].has_value);
  EXPECT_EQ(kForces[1].format, vpiSuppressVal);
  EXPECT_EQ(kForces[1].value, 0);
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

// §38.36.1: a cbDisable is called after a named block containing a system task
// is disabled, with obj that block: the named begin of each of two instances
// of a module, found among the blocks of the instance the disable ran in, and
// a named fork.
TEST_F(EventCallbacksOfARun, ADisableCallbackNamesEachDisabledBlock) {
  Armer() = [] { PlaceEventCallback(cbDisable, nullptr); };
  Run("module child; timeunit 1ns; timeprecision 1ns;\n"
      "  initial begin : blk #2 $display(\"blk ran on\"); end\n"
      "  initial #1 disable blk;\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  child a(); child b();\n"
      "  initial $arm;\n"
      "  initial fork : f #2 $display(\"f ran on\"); join\n"
      "  initial #1 disable f;\n"
      "endmodule\n");
  std::vector<int> kinds;
  for (const EventDelivery& d : DeliveriesOf(cbDisable)) {
    EXPECT_EQ(d.now, 1u);
    EXPECT_EQ(d.obj, d.obj_type == vpiNamedFork ? "f" : "blk");
    kinds.push_back(d.obj_type);
  }
  std::ranges::sort(kinds);
  EXPECT_EQ(kinds,
            (std::vector<int>{vpiNamedBegin, vpiNamedBegin, vpiNamedFork}));
}

// §38.36.1 with §37.77: a cbDisable is called for the block or task the
// disable statement names, resolved upward from where it stands (§23.8): a
// task, the named begin a label creates around a statement (§9.3.5), the
// block a hierarchical name reaches past another of its last name, and a
// block of another instance.
TEST_F(EventCallbacksOfARun, ADisableCallbackIsCalledForTheScopeItNames) {
  Armer() = [] {
    for (const char* name : {"top.t", "top.lbl", "top.b.inner", "top.c.blk"}) {
      vpiHandle scope = TopObject(name);
      EXPECT_NE(scope, nullptr) << name;
      PlaceEventCallback(cbDisable, scope);
    }
  };
  Run("module child; timeunit 1ns; timeprecision 1ns;\n"
      "  initial begin : blk #9 $display(\"blk ran on\"); end\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  child c();\n"
      "  task t; #9 $display(\"t ran on\"); endtask\n"
      "  initial $arm;\n"
      "  initial t;\n"
      "  initial begin lbl: #9 $display(\"lbl ran on\"); end\n"
      "  initial begin : a begin : inner #9 $display(\"a ran on\"); end end\n"
      "  initial begin : b begin : inner #9 $display(\"b ran on\"); end end\n"
      "  initial begin\n"
      "    #1 disable t; #1 disable lbl; #1 disable a.inner;\n"
      "    #1 disable b.inner; #1 disable c.blk;\n"
      "  end\n"
      "endmodule\n");
  std::vector<std::string> names;
  std::vector<uint32_t> times;
  for (const EventDelivery& d : DeliveriesOf(cbDisable)) {
    names.push_back(d.obj);
    times.push_back(d.now);
  }
  EXPECT_EQ(names, (std::vector<std::string>{"t", "lbl", "inner", "blk"}));
  EXPECT_EQ(times, (std::vector<uint32_t>{1, 2, 4, 5}));
}

// §38.36.1: a cbDisable is called after a named block holding a call of a
// system task or system function is disabled, and not after one holding
// none: a block whose one system call is a system function in an expression
// holds one, and a block of assignments alone does not.
TEST_F(EventCallbacksOfARun, ADisableCallbackNeedsASystemCallInTheBlock) {
  Armer() = [] { PlaceEventCallback(cbDisable, nullptr); };
  Run("module top; timeunit 1ns; timeprecision 1ns; int x;\n"
      "  initial $arm;\n"
      "  initial begin : plain #9 x = 1; end\n"
      "  initial begin : calls #9 x = $urandom; end\n"
      "  initial begin #1 disable plain; #1 disable calls; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kDisables = DeliveriesOf(cbDisable);
  ASSERT_EQ(kDisables.size(), 1u);
  EXPECT_EQ(kDisables[0].obj, "calls");
  EXPECT_EQ(kDisables[0].now, 2u);
}

// §38.36.1: a cbDisable placed on a system task call is called, with obj that
// call, after a named block holding it is disabled, here the block around the
// one it is written in; one placed on a call outside that block is not.
TEST_F(EventCallbacksOfARun, ADisableCallbackOnASystemCallFiresWithItsBlock) {
  Armer() = [] {
    PlaceEventCallback(cbDisable,
                       FirstStmtOf(vpiSysTaskCall, TopObject("top.outer")));
    PlaceEventCallback(cbDisable,
                       FirstStmtOf(vpiSysTaskCall, TopObject("top.other")));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  initial $arm;\n"
      "  initial begin : outer\n"
      "    begin : inner #9 $display(\"outer ran on\"); end\n"
      "  end\n"
      "  initial begin : other #9 $display(\"other ran on\"); end\n"
      "  initial #1 disable outer;\n"
      "endmodule\n");
  const std::vector<EventDelivery> kDisables = DeliveriesOf(cbDisable);
  ASSERT_EQ(kDisables.size(), 1u);
  EXPECT_EQ(kDisables[0].obj_type, vpiSysTaskCall);
  EXPECT_EQ(kDisables[0].now, 1u);
}

// §38.36.1 with §9.6.2: a cbDisable is called after a function body disables
// a named block of its own holding a system task call, with obj that block.
TEST_F(EventCallbacksOfARun, ADisableCallbackFiresForAFunctionsBlock) {
  Armer() = [] { PlaceEventCallback(cbDisable, nullptr); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  function int f(int n);\n"
      "    begin : body\n"
      "      if (n > 0) disable body;\n"
      "      $display(\"body ran on\");\n"
      "    end\n"
      "    return n;\n"
      "  endfunction\n"
      "  int r;\n"
      "  initial begin $arm; #1 r = f(1); end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kDisables = DeliveriesOf(cbDisable);
  ASSERT_EQ(kDisables.size(), 1u);
  EXPECT_EQ(kDisables[0].obj, "body");
  EXPECT_EQ(kDisables[0].obj_type, vpiNamedBegin);
  EXPECT_EQ(kDisables[0].now, 1u);
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
