#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <functional>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// What `$put` does each time the design calls it.
std::function<void()>& Putter() {
  static std::function<void()> putter;
  return putter;
}

// A run whose design calls `$put`, which makes the case's puts.
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

  // The integer value `name` holds once the run is over.
  static int IntOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By(name), &value);
    return value.value.integer;
  }
};

// Puts `value` into the object `name` names with `flags`, after `delay` for
// a delay mode; answers the event handle the put returns.
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

// §38.34 with §9.4.2: a value put with vpiNoDelay is an update of the object,
// which resumes an event control waiting on it (#5112).
TEST_F(PutsOfARun, APutWakesAnEventControlOnItsObject) {
  Putter() = [] { PutInt("top.v", 5, vpiNoDelay); };
  Run("module top; int v, seen;\n"
      "  always @(v) seen = v;\n"
      "  initial #1 $put;\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.seen"), 5);
}

// §38.34 with §37.33 and §9.4.3: a value put into a class object's property
// resumes a class task waiting on a condition over it (#5113).
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

// §38.34: a put with vpiInertialDelay sets the object once its delay has
// passed, not at once: 6 put at time 1 with a delay of 3 is 0 at time 3 and
// 6 at time 5 (#5114).
TEST_F(PutsOfARun, AnInertialPutTakesEffectAfterItsDelay) {
  Putter() = [] { PutInt("top.v", 6, vpiInertialDelay, 3); };
  Run(kDelayedPut);
  EXPECT_EQ(IntOf("top.v_at3"), 0);
  EXPECT_EQ(IntOf("top.v_at5"), 6);
}

// §38.34: an event a delayed put scheduled and vpiCancelEvent then cancelled
// is taken out of the event queue and never takes place (#5115).
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

// §38.34 with §10.6.2: vpiReleaseFlag releases a net vpiForceFlag forced, the
// net taking at once the value its driver gives, which value_p reports
// (#5116).
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

// §38.34: vpiPureTransportDelay removes no event, so a put of 7 after 1
// leaves the put of 6 after 3 that came first: 7 at time 3, 6 at time 5.
TEST_F(PutsOfARun, APureTransportPutKeepsTheEventsBeforeIt) {
  Putter() = [] {
    PutInt("top.v", 6, vpiPureTransportDelay, 3);
    PutInt("top.v", 7, vpiPureTransportDelay, 1);
  };
  Run(kTwoPutsOneEarlier);
  EXPECT_EQ(IntOf("top.v_at3"), 7);
  EXPECT_EQ(IntOf("top.v_at5"), 6);
}

// §38.34: vpiInertialDelay removes every event pending on the object, so the
// put of 6 after 3 never takes place once a put of 7 after 1 follows it.
TEST_F(PutsOfARun, AnInertialPutRemovesTheEventsPendingOnItsObject) {
  Putter() = [] {
    PutInt("top.v", 6, vpiInertialDelay, 3);
    PutInt("top.v", 7, vpiInertialDelay, 1);
  };
  Run(kTwoPutsOneEarlier);
  EXPECT_EQ(IntOf("top.v_at3"), 7);
  EXPECT_EQ(IntOf("top.v_at5"), 7);
}

// §38.34: vpiTransportDelay removes the events later than its own and keeps
// the earlier ones: of 6 at time 2 and 8 at time 6, a put of 7 at time 4
// keeps the first and removes the second.
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

// §38.34: an event that has already taken place is no event a later put
// removes, and the later put takes effect in its turn.
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

// §38.34 with Table 38-3: a delayed put whose value is no number of its
// format schedules nothing, and the object keeps its value.
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

}  // namespace
}  // namespace delta
