#include <gtest/gtest.h>

#include <vector>

#include "helpers_event_callbacks.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kForcedNet =
    "module top; timeunit 1ns; timeprecision 1ns;\n"
    "  logic [3:0] d = 4'd6; wire [3:0] w; assign w = d;\n"
    "  initial begin $arm; #1 force w = 4'd9; #1 release w; end\n"
    "endmodule\n";

void ExpectForceThenRelease() {
  const std::vector<EventDelivery> kForces = DeliveriesOf(cbForce);
  ASSERT_EQ(kForces.size(), 1u);
  EXPECT_EQ(kForces[0].value, 9);
  EXPECT_EQ(kForces[0].now, 1u);
  const std::vector<EventDelivery> kReleases = DeliveriesOf(cbRelease);
  ASSERT_EQ(kReleases.size(), 1u);
  EXPECT_EQ(kReleases[0].value, 6);
  EXPECT_EQ(kReleases[0].now, 2u);
}

TEST_F(EventCallbacksOfARun, ForceAndReleaseCallbacksOnANetFireWithItsValue) {
  Armer() = [] {
    PlaceEventCallback(cbForce, TopObject("top.w"));
    PlaceEventCallback(cbRelease, TopObject("top.w"));
  };
  Run(kForcedNet);
  ExpectForceThenRelease();
}

TEST_F(EventCallbacksOfARun, ForceAndReleaseCallbacksOnNoObjectSeeANetForce) {
  Armer() = [] {
    PlaceEventCallback(cbForce, nullptr);
    PlaceEventCallback(cbRelease, nullptr);
  };
  Run(kForcedNet);
  ExpectForceThenRelease();
}

TEST_F(EventCallbacksOfARun,
       DISABLED_AForceOfAOneBitNetDeliversItsUnsignedValue) {
  Armer() = [] { PlaceEventCallback(cbForce, TopObject("top.w")); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic d = 0; wire w; assign w = d;\n"
      "  initial begin $arm; #1 force w = 1; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kForces = DeliveriesOf(cbForce);
  ASSERT_EQ(kForces.size(), 1u);
  EXPECT_EQ(kForces[0].value, 1);
}

void PutWithFlag(int flag) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;
  vpi_put_value(TopObject("top.w"), &value, nullptr, flag);
}

TEST_F(EventCallbacksOfARun,
       DISABLED_AForceThroughPutValueCallsTheForceCallbacks) {
  Armer() = [] {
    PlaceEventCallback(cbForce, TopObject("top.w"));
    PlaceEventCallback(cbRelease, TopObject("top.w"));
    PutWithFlag(vpiForceFlag);
    PutWithFlag(vpiReleaseFlag);
  };
  Run("module top; logic d = 0; wire w; assign w = d;\n"
      "  initial $arm;\n"
      "endmodule\n");
  const std::vector<EventDelivery> kForces = DeliveriesOf(cbForce);
  ASSERT_EQ(kForces.size(), 1u);
  EXPECT_EQ(kForces[0].value, 1);
  const std::vector<EventDelivery> kReleases = DeliveriesOf(cbRelease);
  ASSERT_EQ(kReleases.size(), 1u);
  EXPECT_EQ(kReleases[0].value, 0);
}

std::vector<int>& RefusedReasons() {
  static std::vector<int> refused;
  return refused;
}

void PlaceOnBitAndNote(int reason, vpiHandle bit) {
  vpiHandle placed = PlaceEventCallback(reason, bit);
  const PLI_INT32 kLevel = vpi_chk_error(nullptr);
  if (placed == nullptr && kLevel != 0) RefusedReasons().push_back(reason);
}

TEST_F(EventCallbacksOfARun, ReleaseAndDisableCallbacksOnAVarBitAreRefused) {
  RefusedReasons().clear();
  Armer() = [] {
    vpiHandle bit = vpi_handle_by_index(TopObject("top.v"), 1);
    PlaceOnBitAndNote(cbRelease, bit);
    PlaceOnBitAndNote(cbDisable, bit);
  };
  Run("module top; logic [3:0] v; initial $arm; endmodule\n");
  EXPECT_EQ(RefusedReasons(), (std::vector<int>{cbRelease, cbDisable}));
}

TEST_F(EventCallbacksOfARun, ForceAndReleaseCallbacksOnANetBitAreAccepted) {
  RefusedReasons().clear();
  Armer() = [] {
    vpiHandle bit = vpi_handle_by_index(TopObject("top.n"), 1);
    EXPECT_NE(bit, nullptr);
    PlaceOnBitAndNote(cbForce, bit);
    PlaceOnBitAndNote(cbRelease, bit);
  };
  Run("module top; wire [3:0] n; initial $arm; endmodule\n");
  EXPECT_TRUE(RefusedReasons().empty());
}

vpiHandle RhsOfFirstAssignmentIn(const char* block) {
  vpiHandle it = vpi_iterate(vpiStmt, TopObject(block));
  if (it == nullptr) return nullptr;
  while (vpiHandle stmt = vpi_scan(it)) {
    if (vpi_get(vpiType, stmt) == vpiAssignment) {
      vpi_release_handle(it);
      return vpi_handle(vpiRhs, stmt);
    }
  }
  return nullptr;
}

TEST_F(EventCallbacksOfARun, ADisableCallbackOnASystemFunctionCallFires) {
  Armer() = [] {
    PlaceEventCallback(cbDisable, RhsOfFirstAssignmentIn("top.held"));
    PlaceEventCallback(cbDisable, RhsOfFirstAssignmentIn("top.free"));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; int x; int y;\n"
      "  initial $arm;\n"
      "  initial begin : held x = $urandom; #9; end\n"
      "  initial begin : free y = $urandom; #9; end\n"
      "  initial #3 disable held;\n"
      "endmodule\n");
  const std::vector<EventDelivery> kDisables = DeliveriesOf(cbDisable);
  ASSERT_EQ(kDisables.size(), 1u);
  EXPECT_EQ(kDisables[0].obj_type, vpiSysFuncCall);
  EXPECT_EQ(kDisables[0].obj, "$urandom");
  EXPECT_EQ(kDisables[0].now, 3u);
}

bool& FunctionPlacementAccepted() {
  static bool accepted = false;
  return accepted;
}

TEST_F(EventCallbacksOfARun, ADisableCallbackOnAFunctionIsAcceptedNotCalled) {
  FunctionPlacementAccepted() = false;
  Armer() = [] {
    FunctionPlacementAccepted() =
        PlaceEventCallback(cbDisable, TopObject("top.f")) != nullptr;
    PlaceEventCallback(cbDisable, TopObject("top.f.body"));
  };
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
  EXPECT_TRUE(FunctionPlacementAccepted());
  const std::vector<EventDelivery> kDisables = DeliveriesOf(cbDisable);
  ASSERT_EQ(kDisables.size(), 1u);
  EXPECT_EQ(kDisables[0].obj_type, vpiNamedBegin);
}

}  // namespace
}  // namespace delta
