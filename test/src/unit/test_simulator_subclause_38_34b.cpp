#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <functional>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::function<void()>& Putter() {
  static std::function<void()> putter;
  return putter;
}

class PutsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$put");
    data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
      Putter()();
      return 0;
    };
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static int IntOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By(name), &value);
    return value.value.integer;
  }
};

vpiHandle PutInt(const char* name, int value, int flags, uint32_t delay = 0) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = value;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = delay;
  return vpi_put_value(vpi_handle_by_name(VpiText(name), nullptr), &val, &time,
                       flags);
}

TEST_F(PutsOfARun, APutWakesAnEventControlOnItsObject) {
  Putter() = [] { PutInt("top.v", 5, vpiNoDelay); };
  Run("module top; int v, seen;\n"
      "  always @(v) seen = v;\n"
      "  initial #1 $put;\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.seen"), 5);
}

TEST_F(PutsOfARun, APutIntoAClassPropertyWakesATaskWaitingOnIt) {
  Putter() = [] {
    vpiHandle obj =
        vpi_handle(vpiClassObj, vpi_handle_by_name(VpiText("top.c"), nullptr));
    vpiHandle it = vpi_iterate(vpiVariables, obj);
    for (vpiHandle v = it != nullptr ? vpi_scan(it) : nullptr; v != nullptr;
         v = vpi_scan(it)) {
      if (std::strcmp(vpi_get_str(vpiName, v), "val") != 0) continue;
      s_vpi_value val = {};
      val.format = vpiIntVal;
      val.value.integer = 9;
      vpi_put_value(v, &val, nullptr, vpiNoDelay);
    }
  };
  Run("module top; int saw = 0;\n"
      "  class C; int val;\n"
      "    task wait_for_nine(); wait (val == 9); saw = 1; endtask\n"
      "  endclass\n"
      "  C c = new;\n"
      "  initial begin fork c.wait_for_nine(); join_none #4 $put; #1; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.saw"), 1);
}

constexpr const char* kDelayedPut =
    "module top; timeunit 1ns; timeprecision 1ns; int v, v_at3, v_at5;\n"
    "  initial begin #1 $put; #2 v_at3 = v; #2 v_at5 = v; end\n"
    "endmodule\n";

TEST_F(PutsOfARun, AnInertialPutTakesEffectAfterItsDelay) {
  Putter() = [] { PutInt("top.v", 6, vpiInertialDelay, 3); };
  Run(kDelayedPut);
  EXPECT_EQ(IntOf("top.v_at3"), 0);
  EXPECT_EQ(IntOf("top.v_at5"), 6);
}

TEST_F(PutsOfARun, ACancelledPutNeverTakesEffect) {
  Putter() = [] {
    vpiHandle event = PutInt("top.v", 7, vpiTransportDelay | vpiReturnEvent, 2);
    vpi_put_value(event, nullptr, nullptr, vpiCancelEvent);
  };
  Run(kDelayedPut);
  EXPECT_EQ(IntOf("top.v_at5"), 0);
}

int& ReleasedValue() {
  static int released = -1;
  return released;
}

TEST_F(PutsOfARun, AReleasedNetTakesItsDriversValue) {
  ReleasedValue() = -1;
  Putter() = [] {
    static int calls = 0;
    if (calls++ % 2 == 0) {
      PutInt("top.w", 0, vpiForceFlag);
      return;
    }
    s_vpi_value val = {};
    val.format = vpiIntVal;
    vpi_put_value(vpi_handle_by_name(VpiText("top.w"), nullptr), &val, nullptr,
                  vpiReleaseFlag);
    ReleasedValue() = val.value.integer;
  };
  Run("module top; logic d = 1; wire w = d; logic w_at2;\n"
      "  initial begin #1 $put; #1 w_at2 = w; #1 $put; #1; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.w_at2"), 0);
  EXPECT_EQ(ReleasedValue(), 1);
  EXPECT_EQ(IntOf("top.w"), 1);
}

constexpr const char* kTwoPutsOneEarlier =
    "module top; timeunit 1ns; timeprecision 1ns; int v, v_at3, v_at5, v_at7;\n"
    "  initial begin #1 $put; #2 v_at3 = v; #2 v_at5 = v; #2 v_at7 = v; end\n"
    "endmodule\n";

TEST_F(PutsOfARun, APureTransportPutKeepsTheEventsBeforeIt) {
  Putter() = [] {
    PutInt("top.v", 6, vpiPureTransportDelay, 3);
    PutInt("top.v", 7, vpiPureTransportDelay, 1);
  };
  Run(kTwoPutsOneEarlier);
  EXPECT_EQ(IntOf("top.v_at3"), 7);
  EXPECT_EQ(IntOf("top.v_at5"), 6);
}

TEST_F(PutsOfARun, AnInertialPutRemovesTheEventsPendingOnItsObject) {
  Putter() = [] {
    PutInt("top.v", 6, vpiInertialDelay, 3);
    PutInt("top.v", 7, vpiInertialDelay, 1);
  };
  Run(kTwoPutsOneEarlier);
  EXPECT_EQ(IntOf("top.v_at3"), 7);
  EXPECT_EQ(IntOf("top.v_at5"), 7);
}

TEST_F(PutsOfARun, ATransportPutRemovesOnlyTheLaterEvents) {
  Putter() = [] {
    PutInt("top.v", 6, vpiTransportDelay, 1);
    PutInt("top.v", 8, vpiTransportDelay, 5);
    PutInt("top.v", 7, vpiTransportDelay, 3);
  };
  Run(kTwoPutsOneEarlier);
  EXPECT_EQ(IntOf("top.v_at3"), 6);
  EXPECT_EQ(IntOf("top.v_at5"), 7);
  EXPECT_EQ(IntOf("top.v_at7"), 7);
}

TEST_F(PutsOfARun, APutAfterAnEarlierOneTookPlaceTakesEffect) {
  Putter() = [] {
    static int calls = 0;
    PutInt("top.v", calls++ == 0 ? 6 : 7, vpiInertialDelay, 1);
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; int v, v_at3, v_at5;\n"
      "  initial begin #1 $put; #2 v_at3 = v; $put; #2 v_at5 = v; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.v_at3"), 6);
  EXPECT_EQ(IntOf("top.v_at5"), 7);
}

TEST_F(PutsOfARun, ADelayedPutOfAnUndecodableValueSchedulesNothing) {
  Putter() = [] {
    s_vpi_value val = {};
    val.format = vpiBinStrVal;
    val.value.str = VpiText("2");
    s_vpi_time time = {};
    time.type = vpiSimTime;
    time.low = 1;
    vpi_put_value(vpi_handle_by_name(VpiText("top.v"), nullptr), &val, &time,
                  vpiInertialDelay);
  };
  Run(kTwoPutsOneEarlier);
  EXPECT_EQ(IntOf("top.v_at3"), 0);
}

TEST_F(PutsOfARun, APutToANamedEventTriggersIt) {
  Putter() = [] {
    vpi_put_value(vpi_handle_by_name(VpiText("top.ev"), nullptr), nullptr,
                  nullptr, vpiNoDelay);
  };
  Run("module top; event ev; int seen = 0, fired = 0;\n"
      "  initial begin @ev; seen = 1; end\n"
      "  initial begin #1 $put; #0 fired = ev.triggered; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.seen"), 1);
  EXPECT_EQ(IntOf("top.fired"), 1);
}

TEST_F(PutsOfARun, APutToAPartOfANettypeNetIsRefused) {
  Run("module top;\n"
      "  nettype logic [7:4] n4;\n"
      "  n4 n;\n"
      "endmodule\n");
  vpiHandle bits = vpi_iterate(vpiBit, By("top.n"));
  ASSERT_NE(bits, nullptr);
  vpiHandle bit = vpi_scan(bits);
  ASSERT_NE(bit, nullptr);
  s_vpi_value before = {};
  before.format = vpiBinStrVal;
  vpi_get_value(By("top.n"), &before);
  const std::string kBefore = before.value.str;
  s_vpi_value one = {};
  one.format = vpiScalarVal;
  one.value.scalar = vpi1;
  vpi_put_value(bit, &one, nullptr, vpiNoDelay);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
  s_vpi_value after = {};
  after.format = vpiBinStrVal;
  vpi_get_value(By("top.n"), &after);
  EXPECT_EQ(std::string(after.value.str), kBefore);
  s_vpi_value whole = {};
  whole.format = vpiIntVal;
  whole.value.integer = 5;
  vpi_put_value(By("top.n"), &whole, nullptr, vpiNoDelay);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

TEST_F(PutsOfARun, ARealVariableHoldsTheRealOrIntegerPut) {
  Run("module top; real r; shortreal s; initial $noop; endmodule\n");
  s_vpi_value half = {};
  half.format = vpiRealVal;
  half.value.real = 2.5;
  vpi_put_value(By("top.r"), &half, nullptr, vpiNoDelay);
  s_vpi_value three = {};
  three.format = vpiIntVal;
  three.value.integer = -3;
  vpi_put_value(By("top.s"), &three, nullptr, vpiNoDelay);
  s_vpi_value read = {};
  read.format = vpiRealVal;
  vpi_get_value(By("top.r"), &read);
  EXPECT_DOUBLE_EQ(read.value.real, 2.5);
  vpi_get_value(By("top.s"), &read);
  EXPECT_DOUBLE_EQ(read.value.real, -3.0);
}

TEST_F(PutsOfARun, ARealMemberOfAStructureHoldsTheRealPut) {
  Run("module top; struct { real r; int i; } s; initial $noop; endmodule\n");
  s_vpi_value half = {};
  half.format = vpiRealVal;
  half.value.real = 2.5;
  vpi_put_value(By("top.s.r"), &half, nullptr, vpiNoDelay);
  s_vpi_value read = {};
  read.format = vpiRealVal;
  vpi_get_value(By("top.s.r"), &read);
  EXPECT_DOUBLE_EQ(read.value.real, 2.5);
}

double RealAfterPut(s_vpi_value put) {
  vpi_put_value(vpi_handle_by_name(VpiText("top.r"), nullptr), &put, nullptr,
                vpiNoDelay);
  s_vpi_value read = {};
  read.format = vpiRealVal;
  vpi_get_value(vpi_handle_by_name(VpiText("top.r"), nullptr), &read);
  return read.value.real;
}

TEST_F(PutsOfARun, ARealVariableTakesAnIntegralFormatAsItsInteger) {
  Run("module top; real r; initial $noop; endmodule\n");
  s_vpi_value dec = {};
  dec.format = vpiDecStrVal;
  dec.value.str = VpiText("3");
  EXPECT_DOUBLE_EQ(RealAfterPut(dec), 3.0);
  s_vpi_value hex = {};
  hex.format = vpiHexStrVal;
  hex.value.str = VpiText("1x");
  EXPECT_DOUBLE_EQ(RealAfterPut(hex), 16.0);
  s_vpi_value scalar = {};
  scalar.format = vpiScalarVal;
  scalar.value.scalar = vpi1;
  EXPECT_DOUBLE_EQ(RealAfterPut(scalar), 1.0);
  s_vpi_value nothing = {};
  nothing.format = vpiVectorVal;
  EXPECT_DOUBLE_EQ(RealAfterPut(nothing), 1.0);
}

TEST_F(PutsOfARun, ARealReadAsAVectorIsPutBackAsItself) {
  Run("module top; real r; initial $noop; endmodule\n");
  s_vpi_value minus = {};
  minus.format = vpiRealVal;
  minus.value.real = -4.0;
  RealAfterPut(minus);
  s_vpi_value read = {};
  read.format = vpiVectorVal;
  vpi_get_value(By("top.r"), &read);
  ASSERT_NE(read.value.vector, nullptr);
  std::vector<s_vpi_vecval> held(read.value.vector, read.value.vector + 2);
  s_vpi_value zero = {};
  zero.format = vpiIntVal;
  EXPECT_DOUBLE_EQ(RealAfterPut(zero), 0.0);
  s_vpi_value back = {};
  back.format = vpiVectorVal;
  back.value.vector = held.data();
  EXPECT_DOUBLE_EQ(RealAfterPut(back), -4.0);
}

int string_put_error = 0;

class RealFunctionOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    string_put_error = 0;
    s_vpi_systf_data data = {};
    data.type = vpiSysFunc;
    data.sysfunctype = vpiRealFunc;
    data.tfname = VpiText("$half_of_five");
    data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
      vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
      s_vpi_value text = {};
      text.format = vpiStringVal;
      text.value.str = VpiText("2.5");
      vpi_put_value(call, &text, nullptr, vpiNoDelay);
      string_put_error = vpi_chk_error(nullptr);
      s_vpi_value real = {};
      real.format = vpiRealVal;
      real.value.real = 2.5;
      vpi_put_value(call, &real, nullptr, vpiNoDelay);
      return 0;
    };
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
};

TEST_F(RealFunctionOfARun, ItReturnsTheRealPutAndRefusesAString) {
  Run("module top; real r; initial r = $half_of_five; endmodule\n");
  s_vpi_value value = {};
  value.format = vpiRealVal;
  vpi_get_value(By("top.r"), &value);
  EXPECT_DOUBLE_EQ(value.value.real, 2.5);
  EXPECT_NE(string_put_error, 0);
}

std::string StringOf(vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiStringVal;
  vpi_get_value(obj, &value);
  return value.value.str == nullptr ? "" : value.value.str;
}

int IntValueOf(vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(obj, &value);
  return value.value.integer;
}

void ExpectPutTargetRefused(vpiHandle target, s_vpi_value put) {
  EXPECT_EQ(vpi_put_value(target, &put, nullptr, vpiNoDelay), nullptr);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_STREQ(info.message,
               "vpi_put_value(): a value can be put only to a net, a "
               "variable, a variable select, a named event, a system "
               "function call, a sequential UDP or a scheduled event");
}

TEST_F(PutsOfARun, APutToAParameterSpecparamOrTableEntryIsRefused) {
  Run("primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; parameter P = 5; specparam S = 7; wire o; reg i;\n"
      "  inv g(o, i);\n"
      "endmodule\n");
  const std::vector<vpiHandle> kRows =
      ObjectsOf(vpiTableEntry, Named(vpiUdpDefn, nullptr, "inv"));
  ASSERT_EQ(kRows.size(), 2u);
  const vpiHandle kTargets[] = {Named(vpiParameter, By("top"), "P"),
                                Named(vpiSpecParam, By("top"), "S"), kRows[0]};
  for (vpiHandle target : kTargets) {
    ASSERT_NE(target, nullptr);
    s_vpi_value put = {};
    put.format = vpiStringVal;
    put.value.str = VpiText("(");
    ExpectPutTargetRefused(target, put);
  }
  EXPECT_EQ(IntValueOf(kTargets[0]), 5);
  EXPECT_EQ(IntValueOf(kTargets[1]), 7);
  EXPECT_EQ(StringOf(kRows[0]), "0 : 1");
}

TEST_F(PutsOfARun, APutToABitSelectOrAPartSelectIsRefused) {
  Run("module top; integer n = 5; logic [7:0] r = 8'hA5; logic [2:0] i = 1;\n"
      "  wire b; wire [3:0] p, q;\n"
      "  assign b = n[2]; assign p = r[7:4]; assign q = r[i+:4];\n"
      "endmodule\n");
  std::vector<int> kinds;
  for (vpiHandle assign : ObjectsOf(vpiContAssign, By("top"))) {
    vpiHandle select = vpi_handle(vpiRhs, assign);
    kinds.push_back(vpi_get(vpiType, select));
    s_vpi_value put = {};
    put.format = vpiIntVal;
    ExpectPutTargetRefused(select, put);
  }
  EXPECT_EQ(kinds, (std::vector<int>{vpiBitSelect, vpiPartSelect,
                                     vpiIndexedPartSelect}));
  EXPECT_EQ(IntOf("top.n"), 5);
  EXPECT_EQ(IntOf("top.r"), 0xA5);
}

}  // namespace
}  // namespace delta
