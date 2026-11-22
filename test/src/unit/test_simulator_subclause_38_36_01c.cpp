#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "helpers_event_callbacks.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct FormattedDelivery {
  bool value_null = true;
  int format = 0;
  std::string str;
  double real = 0;
  int scalar = 0;
  int integer = 0;
  uint32_t time_high = 0;
  uint32_t time_low = 0;
  uint32_t aval = 0;
  uint32_t bval = 0;
  bool time_null = true;
  int time_type = 0;
  double real_time = 0;
};

std::vector<FormattedDelivery>& FormattedDeliveries() {
  static std::vector<FormattedDelivery> deliveries;
  return deliveries;
}

void CopyValue(const s_vpi_value& v, FormattedDelivery& d) {
  d.format = v.format;
  switch (v.format) {
    case vpiBinStrVal:
    case vpiOctStrVal:
    case vpiDecStrVal:
    case vpiHexStrVal:
    case vpiStringVal:
      d.str = v.value.str == nullptr ? "" : v.value.str;
      break;
    case vpiRealVal:
      d.real = v.value.real;
      break;
    case vpiScalarVal:
      d.scalar = v.value.scalar;
      break;
    case vpiTimeVal:
      if (v.value.time != nullptr) {
        d.time_high = v.value.time->high;
        d.time_low = v.value.time->low;
      }
      break;
    case vpiVectorVal:
      if (v.value.vector != nullptr) {
        d.aval = v.value.vector[0].aval;
        d.bval = v.value.vector[0].bval;
      }
      break;
    default:
      d.integer = v.value.integer;
  }
}

PLI_INT32 RecordFormatted(p_cb_data cb) {
  FormattedDelivery d;
  d.value_null = cb->value == nullptr;
  if (cb->value != nullptr) CopyValue(*cb->value, d);
  d.time_null = cb->time == nullptr;
  if (cb->time != nullptr) {
    d.time_type = cb->time->type;
    d.real_time = cb->time->real;
  }
  FormattedDeliveries().push_back(d);
  return 0;
}

vpiHandle PlaceFormatted(vpiHandle obj, int format, int time_type) {
  static s_vpi_time time;
  static s_vpi_value value;
  time.type = time_type;
  value.format = format;
  s_cb_data data = {};
  data.reason = cbValueChange;
  data.cb_rtn = &RecordFormatted;
  data.obj = obj;
  data.time = &time;
  data.value = &value;
  return vpi_register_cb(&data);
}

struct FormatCase {
  const char* decl;
  const char* change;
  int format;
  int time_type;
};

FormatCase& Pending() {
  static FormatCase pending;
  return pending;
}

class FormattedCallbacksOfARun : public EventCallbacksOfARun {
 protected:
  void SetUp() override {
    EventCallbacksOfARun::SetUp();
    FormattedDeliveries().clear();
  }

  FormattedDelivery OnlyDelivery(const FormatCase& c) {
    Pending() = c;
    Armer() = [] {
      PlaceFormatted(TopObject("top.v"), Pending().format, Pending().time_type);
    };
    Run(std::string("module top; timeunit 1ns; timeprecision 1ps; ") + c.decl +
        ";\n  initial begin $arm; #1.5 " + c.change + "; end\nendmodule\n");
    EXPECT_EQ(FormattedDeliveries().size(), 1u);
    return FormattedDeliveries().empty() ? FormattedDelivery{}
                                         : FormattedDeliveries()[0];
  }

  FormattedDelivery OnByte(int format) {
    return OnlyDelivery(
        {"logic [7:0] v = 0", "v = 8'b1010_0101", format, vpiSimTime});
  }
};

TEST_F(FormattedCallbacksOfARun, ABinaryStringFormatDeliversBinaryDigits) {
  const FormattedDelivery kGot = OnlyDelivery(
      {"logic [7:0] v = 0", "v = 8'b10x1_z010", vpiBinStrVal, vpiSimTime});
  EXPECT_EQ(kGot.format, vpiBinStrVal);
  EXPECT_EQ(kGot.str, "10x1z010");
}

TEST_F(FormattedCallbacksOfARun, AnOctalStringFormatDeliversOctalDigits) {
  const FormattedDelivery kGot = OnByte(vpiOctStrVal);
  EXPECT_EQ(kGot.format, vpiOctStrVal);
  EXPECT_EQ(kGot.str, "245");
}

TEST_F(FormattedCallbacksOfARun, ADecimalStringFormatDeliversDecimalDigits) {
  const FormattedDelivery kGot = OnByte(vpiDecStrVal);
  EXPECT_EQ(kGot.format, vpiDecStrVal);
  EXPECT_EQ(kGot.str, "165");
}

TEST_F(FormattedCallbacksOfARun, AHexStringFormatDeliversHexDigits) {
  const FormattedDelivery kGot = OnByte(vpiHexStrVal);
  EXPECT_EQ(kGot.format, vpiHexStrVal);
  EXPECT_EQ(kGot.str, "a5");
}

TEST_F(FormattedCallbacksOfARun, AScalarFormatDeliversTheScalarState) {
  const FormattedDelivery kGot =
      OnlyDelivery({"logic v = 0", "v = 1'bz", vpiScalarVal, vpiSimTime});
  EXPECT_EQ(kGot.format, vpiScalarVal);
  EXPECT_EQ(kGot.scalar, vpiZ);
}

TEST_F(FormattedCallbacksOfARun, ARealFormatDeliversADouble) {
  const FormattedDelivery kGot =
      OnlyDelivery({"real v = 0.0", "v = 2.25", vpiRealVal, vpiSimTime});
  EXPECT_EQ(kGot.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(kGot.real, 2.25);
}

TEST_F(FormattedCallbacksOfARun, AStringFormatDeliversTheCharacters) {
  const FormattedDelivery kGot = OnlyDelivery(
      {"logic [23:0] v = 0", "v = \"abc\"", vpiStringVal, vpiSimTime});
  EXPECT_EQ(kGot.format, vpiStringVal);
  EXPECT_EQ(kGot.str, "abc");
}

TEST_F(FormattedCallbacksOfARun, ATimeFormatDeliversBothHalves) {
  const FormattedDelivery kGot = OnlyDelivery(
      {"time v = 0", "v = 64'h3_0000_0007", vpiTimeVal, vpiSimTime});
  EXPECT_EQ(kGot.format, vpiTimeVal);
  EXPECT_EQ(kGot.time_high, 3u);
  EXPECT_EQ(kGot.time_low, 7u);
}

TEST_F(FormattedCallbacksOfARun, AVectorFormatDeliversAvalAndBval) {
  const FormattedDelivery kGot = OnlyDelivery(
      {"logic [3:0] v = 0", "v = 4'b1x0z", vpiVectorVal, vpiSimTime});
  EXPECT_EQ(kGot.format, vpiVectorVal);
  EXPECT_EQ(kGot.aval, 0xCu);
  EXPECT_EQ(kGot.bval, 0x5u);
}

TEST_F(FormattedCallbacksOfARun, AnObjTypeFormatOnARealDeliversARealFormat) {
  const FormattedDelivery kGot =
      OnlyDelivery({"real v = 0.0", "v = 4.5", vpiObjTypeVal, vpiSimTime});
  EXPECT_EQ(kGot.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(kGot.real, 4.5);
}

TEST_F(FormattedCallbacksOfARun, AnObjTypeFormatOnAnIntDeliversAnIntFormat) {
  const FormattedDelivery kGot =
      OnlyDelivery({"int v = 0", "v = 9", vpiObjTypeVal, vpiSimTime});
  EXPECT_EQ(kGot.format, vpiIntVal);
  EXPECT_EQ(kGot.integer, 9);
}

TEST_F(FormattedCallbacksOfARun, AScaledRealTimeIsInTheObjectsTimeUnit) {
  const FormattedDelivery kGot =
      OnlyDelivery({"int v = 0", "v = 1", vpiIntVal, vpiScaledRealTime});
  ASSERT_FALSE(kGot.time_null);
  EXPECT_EQ(kGot.time_type, vpiScaledRealTime);
  EXPECT_DOUBLE_EQ(kGot.real_time, 1.5);
}

TEST_F(FormattedCallbacksOfARun, ASuppressedTimeDeliversNoTime) {
  const FormattedDelivery kGot =
      OnlyDelivery({"int v = 0", "v = 1", vpiIntVal, vpiSuppressTime});
  EXPECT_TRUE(kGot.time_null || kGot.time_type == vpiSuppressTime);
}

bool& OddTimePlacementRefused() {
  static bool refused = false;
  return refused;
}

TEST_F(FormattedCallbacksOfARun, DISABLED_ATimeTypeOutsideTheThreeIsRefused) {
  OddTimePlacementRefused() = false;
  Armer() = [] {
    vpiHandle placed = PlaceFormatted(TopObject("top.v"), vpiIntVal, 7);
    const PLI_INT32 kLevel = vpi_chk_error(nullptr);
    OddTimePlacementRefused() = placed == nullptr && kLevel != 0;
  };
  Run("module top; int v = 0; initial begin $arm; #1 v = 1; end endmodule\n");
  EXPECT_TRUE(OddTimePlacementRefused());
  EXPECT_TRUE(FormattedDeliveries().empty());
}

void ExpectIndexAndValue(int index, int value) {
  const std::vector<EventDelivery> kChanges = DeliveriesOf(cbValueChange);
  ASSERT_EQ(kChanges.size(), 1u);
  EXPECT_EQ(kChanges[0].index, index);
  EXPECT_EQ(kChanges[0].value, value);
}

TEST_F(EventCallbacksOfARun, AMultidimensionalMemberReportsItsRightmostIndex) {
  Armer() = [] {
    PlaceEventCallback(
        cbValueChange,
        vpi_handle_by_index(vpi_handle_by_index(TopObject("top.m"), 1), 2));
  };
  Run("module top; int m[2][3];\n"
      "  initial begin $arm; #1 m[0][2] = 3; #1 m[1][2] = 4; end\n"
      "endmodule\n");
  ExpectIndexAndValue(2, 4);
}

TEST_F(EventCallbacksOfARun, AnOffsetRangeMemberReportsItsDeclaredIndex) {
  Armer() = [] {
    PlaceEventCallback(cbValueChange,
                       vpi_handle_by_index(TopObject("top.a"), 6));
  };
  Run("module top; int a[5:8];\n"
      "  initial begin $arm; #1 a[5] = 3; #1 a[6] = 4; end\n"
      "endmodule\n");
  ExpectIndexAndValue(6, 4);
}

TEST_F(EventCallbacksOfARun, ADescendingRangeMemberReportsItsDeclaredIndex) {
  Armer() = [] {
    PlaceEventCallback(cbValueChange,
                       vpi_handle_by_index(TopObject("top.d"), 5));
  };
  Run("module top; int d[7:4];\n"
      "  initial begin $arm; #1 d[6] = 3; #1 d[5] = 4; end\n"
      "endmodule\n");
  ExpectIndexAndValue(5, 4);
}

std::vector<uint32_t> ChangeTimes() {
  std::vector<uint32_t> times;
  for (const EventDelivery& d : DeliveriesOf(cbValueChange)) {
    times.push_back(d.time);
  }
  return times;
}

TEST_F(EventCallbacksOfARun, AClassVarCallbackFiresWhenItsReferenceChanges) {
  Armer() = [] { PlaceEventCallback(cbValueChange, TopObject("top.c")); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  class C; endclass C c; C d;\n"
      "  initial begin $arm;\n"
      "    #1 c = new; #1 d = c; #1 c = d; #1 c = null; #1 c = new;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ChangeTimes(), (std::vector<uint32_t>{1, 4, 5}));
  for (const EventDelivery& d : DeliveriesOf(cbValueChange)) {
    EXPECT_FALSE(d.has_value);
  }
}

bool& WatchAccepted() {
  static bool accepted = false;
  return accepted;
}

void Watch(vpiHandle obj) {
  WatchAccepted() =
      obj != nullptr && PlaceEventCallback(cbValueChange, obj) != nullptr;
}

constexpr const char* kGatedNet =
    "module top; timeunit 1ns; timeprecision 1ns;\n"
    "  logic a = 0; logic b = 0; wire w; assign w = a & b;\n"
    "  initial begin #1 $arm; #1 a = 1; #1 b = 1; #1 a = 0; end\n"
    "endmodule\n";

TEST_F(EventCallbacksOfARun, ANetCallbackFiresOnlyWhenTheNetChanges) {
  Armer() = [] { Watch(TopObject("top.w")); };
  Run(kGatedNet);
  EXPECT_TRUE(WatchAccepted());
  EXPECT_EQ(ChangeTimes(), (std::vector<uint32_t>{3, 4}));
}

vpiHandle FirstOf(int type, vpiHandle in) {
  vpiHandle it = vpi_iterate(type, in);
  if (it == nullptr) return nullptr;
  vpiHandle first = vpi_scan(it);
  if (first != nullptr) vpi_release_handle(it);
  return first;
}

TEST_F(EventCallbacksOfARun,
       DISABLED_AnOperationCallbackFiresOnlyWhenItsResultChanges) {
  Armer() = [] {
    Watch(vpi_handle(vpiRhs, FirstOf(vpiContAssign, TopObject("top"))));
  };
  Run(kGatedNet);
  EXPECT_TRUE(WatchAccepted());
  EXPECT_EQ(ChangeTimes(), (std::vector<uint32_t>{3, 4}));
}

TEST_F(EventCallbacksOfARun,
       DISABLED_APartSelectCallbackFiresOnlyWhenItsBitsChange) {
  Armer() = [] {
    Watch(vpi_handle(vpiRhs, FirstOf(vpiContAssign, TopObject("top"))));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic [3:0] v = 0; wire [1:0] p; assign p = v[2:1];\n"
      "  initial begin #1 $arm; #1 v = 4'b1001; #1 v = 4'b0010; end\n"
      "endmodule\n");
  EXPECT_TRUE(WatchAccepted());
  EXPECT_EQ(ChangeTimes(), (std::vector<uint32_t>{3}));
}

TEST_F(EventCallbacksOfARun,
       DISABLED_APrimitiveTerminalCallbackFiresWhenItChanges) {
  Armer() = [] {
    Watch(FirstOf(vpiPrimTerm, FirstOf(vpiPrimitive, TopObject("top"))));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic a = 0; logic b = 0; wire y; and g(y, a, b);\n"
      "  initial begin #1 $arm; #1 a = 1; #1 b = 1; end\n"
      "endmodule\n");
  EXPECT_TRUE(WatchAccepted());
  EXPECT_EQ(ChangeTimes(), (std::vector<uint32_t>{3}));
}

TEST_F(EventCallbacksOfARun, DISABLED_APortCallbackFiresWhenItsValueChanges) {
  Armer() = [] { Watch(FirstOf(vpiPort, TopObject("top.u"))); };
  Run("module sub(input logic i); timeunit 1ns; timeprecision 1ns;\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic s = 0; sub u(.i(s));\n"
      "  initial begin #1 $arm; #1 s = 0; #1 s = 1; end\n"
      "endmodule\n");
  EXPECT_TRUE(WatchAccepted());
  EXPECT_EQ(ChangeTimes(), (std::vector<uint32_t>{3}));
}

TEST_F(EventCallbacksOfARun, DISABLED_AQueueElementCallbackFiresWhenItChanges) {
  Armer() = [] { Watch(vpi_handle_by_index(TopObject("top.q"), 0)); };
  Run("module top; timeunit 1ns; timeprecision 1ns; int q[$] = '{1};\n"
      "  initial begin $arm; #1 q = '{5, 6}; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kChanges = DeliveriesOf(cbValueChange);
  ASSERT_EQ(kChanges.size(), 1u);
  EXPECT_EQ(kChanges[0].value, 5);
}

class ExcludedValueChanges : public EventCallbacksOfARun {
 protected:
  void ExpectNeverCalled(const std::string& decl, const std::string& change) {
    Armer() = [] { Watch(TopObject("top.v")); };
    Run("module top; timeunit 1ns; timeprecision 1ns;\n  " + decl +
        ";\n  initial begin $arm; #1 " + change + "; end\nendmodule\n");
    EXPECT_TRUE(WatchAccepted());
    EXPECT_TRUE(DeliveriesOf(cbValueChange).empty());
  }
};

TEST_F(ExcludedValueChanges, AClassObjectCallbackIsAcceptedAndNeverCalled) {
  Armer() = [] { Watch(vpi_handle(vpiClassObj, TopObject("top.c"))); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  class C; int x; endclass C c = new;\n"
      "  initial begin $arm; #1 c.x = 4; #1 c = new; end\n"
      "endmodule\n");
  EXPECT_TRUE(WatchAccepted());
  EXPECT_TRUE(DeliveriesOf(cbValueChange).empty());
}

TEST_F(ExcludedValueChanges, ADynamicArrayCallbackIsAcceptedAndNeverCalled) {
  ExpectNeverCalled("int v[] = '{1, 2}", "v = '{3, 4}");
}

TEST_F(ExcludedValueChanges, DISABLED_AStringCallbackIsAcceptedAndNeverCalled) {
  ExpectNeverCalled("string v = \"a\"", "v = \"b\"");
}

TEST_F(ExcludedValueChanges, AQueueCallbackIsAcceptedAndNeverCalled) {
  ExpectNeverCalled("int v[$] = '{1}", "v = '{2}");
}

TEST_F(ExcludedValueChanges,
       AnAssociativeArrayCallbackIsAcceptedAndNeverCalled) {
  ExpectNeverCalled("int v[int]", "v[3] = 4");
}

vpiHandle PropertyNamed(vpiHandle object, const std::string& name) {
  vpiHandle it = vpi_iterate(vpiVariables, object);
  while (vpiHandle var = it == nullptr ? nullptr : vpi_scan(it)) {
    if (name == vpi_get_str(vpiName, var)) {
      vpi_release_handle(it);
      return var;
    }
  }
  return nullptr;
}

TEST_F(EventCallbacksOfARun,
       DISABLED_AClassPropertyCallbackFiresForThatPropertyAlone) {
  Armer() = [] {
    Watch(PropertyNamed(vpi_handle(vpiClassObj, TopObject("top.c1")), "x"));
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  class C; int x; int y; endclass C c1 = new; C c2 = new;\n"
      "  initial begin $arm; #1 c1.y = 4; #1 c2.x = 5; #1 c1.x = 3; end\n"
      "endmodule\n");
  EXPECT_TRUE(WatchAccepted());
  const std::vector<EventDelivery> kChanges = DeliveriesOf(cbValueChange);
  ASSERT_EQ(kChanges.size(), 1u);
  EXPECT_EQ(kChanges[0].value, 3);
  EXPECT_EQ(kChanges[0].time, 3u);
}

bool& CreatePlacementRefused() {
  static bool refused = false;
  return refused;
}

TEST_F(EventCallbacksOfARun,
       DISABLED_ACreateObjCallbackOnAClassObjectIsRefused) {
  CreatePlacementRefused() = false;
  Armer() = [] {
    vpiHandle object = vpi_handle(vpiClassObj, TopObject("top.c"));
    if (object == nullptr) return;
    vpiHandle placed = PlaceEventCallback(cbCreateObj, object);
    const PLI_INT32 kLevel = vpi_chk_error(nullptr);
    CreatePlacementRefused() = placed == nullptr && kLevel != 0;
  };
  Run("module top; class C; endclass C c = new;\n"
      "  initial $arm;\n"
      "endmodule\n");
  EXPECT_TRUE(CreatePlacementRefused());
}

}  // namespace
}  // namespace delta
