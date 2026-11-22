#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_assertion_run.h"
#include "helpers_assertion_sites.h"
#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct StaticAssertionInfo {
  std::string name;
  int type = 0;
  vpiHandle instance = nullptr;
  std::string file;
  int line = 0;
};

StaticAssertionInfo ReadStaticInfo(vpiHandle assertion) {
  StaticAssertionInfo info;
  info.name = vpi_get_str(vpiName, assertion);
  info.type = vpi_get(vpiType, assertion);
  info.instance = vpi_handle(vpiInstance, assertion);
  info.file = vpi_get_str(vpiFile, assertion);
  info.line = vpi_get(vpiLineNo, assertion);
  return info;
}

class AssertionStaticInformation : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&vpi_ctx_);
    SetGlobalAssertionApi(&api_);

    dut_.type = vpiModule;
    dut_.name = "dut";
    assertion_.type = vpiAssert;
    assertion_.name = "handshake_p";
    assertion_.file = "dut.sv";
    assertion_.line_no = 42;
    assertion_.parent = &dut_;
    dut_.children = {&assertion_};
  }
  void TearDown() override {
    SetGlobalAssertionApi(nullptr);
    SetGlobalVpiContext(nullptr);
  }

  VpiObject dut_;
  VpiObject assertion_;
  VpiContext vpi_ctx_;
  AssertionApi api_;
};

TEST_F(AssertionStaticInformation,
       TheHandleIsWhatTheStaticInformationIsReadFrom) {
  vpiHandle it = vpi_iterate(vpiAssertion, VpiHandleOf(&dut_));
  ASSERT_NE(it, nullptr);
  vpiHandle assertion = vpi_scan(it);
  ASSERT_EQ(VpiObjectOf(assertion), &assertion_);
  ASSERT_EQ(vpi_scan(it), nullptr);

  StaticAssertionInfo info = ReadStaticInfo(assertion);
  EXPECT_EQ(info.name, "handshake_p");
  EXPECT_EQ(info.type, vpiAssert);
  EXPECT_EQ(VpiObjectOf(info.instance), &dut_);
  EXPECT_EQ(info.file, "dut.sv");
  EXPECT_EQ(info.line, 42);
}

TEST_F(AssertionStaticInformation, TheInformationDoesNotMoveWhileTheRunDoes) {
  StaticAssertionInfo before = ReadStaticInfo(VpiHandleOf(&assertion_));

  api_.NoteAssertionAttemptStarted("handshake_p", 10);
  api_.NoteAssertionAttemptStarted("handshake_p", 20);
  AssertionAttemptInfo attempt;
  attempt.attempt_start_time = 10;
  attempt.fail_expr = "req && !ack";
  api_.DeliverAssertionEvent("handshake_p", cbAssertionFailure, 14, attempt);
  ASSERT_TRUE(api_.Control(vpiAssertionDisable, "handshake_p"));

  ASSERT_FALSE(api_.AssertionEnabled("handshake_p"));

  StaticAssertionInfo after = ReadStaticInfo(VpiHandleOf(&assertion_));
  EXPECT_EQ(after.name, before.name);
  EXPECT_EQ(after.type, before.type);
  EXPECT_EQ(after.instance, before.instance);
  EXPECT_EQ(after.file, before.file);
  EXPECT_EQ(after.line, before.line);
}

struct ElaboratedStaticInfo {
  std::string name;
  int type = 0;
  std::string instance;
  std::string file;
  int line = 0;
  int column = 0;
  std::string clocking_block;
  int clocking_op = 0;
  bool operator==(const ElaboratedStaticInfo&) const = default;
};

std::vector<ElaboratedStaticInfo>& StaticSnapshots() {
  static std::vector<ElaboratedStaticInfo> snapshots;
  return snapshots;
}

void SnapStaticInfo(vpiHandle assertion) {
  ElaboratedStaticInfo info;
  info.name = vpi_get_str(vpiName, assertion);
  info.type = vpi_get(vpiType, assertion);
  info.instance = AssertionSiteFullName(vpi_handle(vpiInstance, assertion));
  info.file = vpi_get_str(vpiFile, assertion);
  info.line = vpi_get(vpiStartLine, assertion);
  info.column = vpi_get(vpiColumn, assertion);
  vpiHandle block = vpi_handle(vpiClockingBlock, assertion);
  info.clocking_block = block == nullptr ? "" : vpi_get_str(vpiName, block);
  vpiHandle event = vpi_handle(vpiClockingEvent, assertion);
  info.clocking_op = event == nullptr ? 0 : vpi_get(vpiOpType, event);
  StaticSnapshots().push_back(info);
}

vpiHandle TheAssertion() {
  return vpi_handle_by_name(VpiText("top.a1"), nullptr);
}

TEST_F(AssertionRun, AnElaboratedAssertionsStaticInformationHoldsThroughARun) {
  StaticSnapshots().clear();
  ArmInTurn({[] {
               SnapStaticInfo(TheAssertion());
               WatchAssertion("top.a1", cbAssertionFailure);
             },
             [] { vpi_control(vpiAssertionDisable, TheAssertion()); },
             [] { SnapStaticInfo(TheAssertion()); }});
  Run("module top; logic clk = 0, a = 0;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  a1: assert property (a);\n"
      "  initial begin\n"
      "    $arm;\n"
      "    #1 clk = 1; #1 clk = 0; #1 clk = 1; #1 clk = 0;\n"
      "    $arm;\n"
      "    #1 clk = 1; #1 clk = 0;\n"
      "    $arm;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(CallsOf(cbAssertionFailure).empty());
  EXPECT_FALSE(api_.AssertionEnabled("top.a1"));
  ASSERT_EQ(StaticSnapshots().size(), 2u);
  EXPECT_EQ(StaticSnapshots()[0].name, "a1");
  EXPECT_EQ(StaticSnapshots()[0].type, vpiAssert);
  EXPECT_EQ(StaticSnapshots()[0].instance, "top");
  EXPECT_EQ(StaticSnapshots()[0].line, 3);
  EXPECT_EQ(StaticSnapshots()[0].clocking_block, "cb");
  EXPECT_EQ(StaticSnapshots()[0].clocking_op, vpiPosedgeOp);
  EXPECT_EQ(StaticSnapshots()[1], StaticSnapshots()[0]);
}

}  // namespace
}  // namespace delta
