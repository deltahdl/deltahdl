#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "helpers_event_callbacks.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<int> SizesDelivered() {
  std::vector<int> sizes;
  for (const EventDelivery& d : DeliveriesOf(cbSizeChange)) {
    sizes.push_back(d.value);
  }
  return sizes;
}

std::vector<uint32_t> SizeTimes() {
  std::vector<uint32_t> times;
  for (const EventDelivery& d : DeliveriesOf(cbSizeChange)) {
    times.push_back(d.time);
  }
  return times;
}

TEST_F(EventCallbacksOfARun, ADynamicArrayReportsEachNewAndDelete) {
  Armer() = [] { PlaceEventCallback(cbSizeChange, TopObject("top.d")); };
  Run("module top; timeunit 1ns; timeprecision 1ns; int d[];\n"
      "  initial begin $arm;\n"
      "    #1 d = new[3]; #1 d = new[5](d); #1 d.delete();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(SizesDelivered(), (std::vector<int>{3, 5, 0}));
  EXPECT_EQ(SizeTimes(), (std::vector<uint32_t>{1, 2, 3}));
}

TEST_F(EventCallbacksOfARun,
       DISABLED_AnAssociativeArrayReportsInsertsAndDeletesOnly) {
  Armer() = [] { PlaceEventCallback(cbSizeChange, TopObject("top.aa")); };
  Run("module top; timeunit 1ns; timeprecision 1ns; int aa[int];\n"
      "  initial begin $arm;\n"
      "    #1 aa[1] = 5; #1 aa[2] = 6; #1 aa[1] = 7; #1 aa.delete(2);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(SizesDelivered(), (std::vector<int>{1, 2, 1}));
  EXPECT_EQ(SizeTimes(), (std::vector<uint32_t>{1, 2, 4}));
}

TEST_F(EventCallbacksOfARun, AStringReportsOnlyAChangeOfLength) {
  Armer() = [] { PlaceEventCallback(cbSizeChange, TopObject("top.s")); };
  Run("module top; timeunit 1ns; timeprecision 1ns; string s;\n"
      "  initial begin $arm;\n"
      "    #1 s = \"ab\"; #1 s = \"cd\"; #1 s = \"xyz\";\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(SizesDelivered(), (std::vector<int>{2, 3}));
  EXPECT_EQ(SizeTimes(), (std::vector<uint32_t>{1, 3}));
}

TEST_F(EventCallbacksOfARun, AFixedSizeVariableNeverReportsASizeChange) {
  Armer() = [] {
    for (const char* name : {"top.f", "top.i", "top.v"}) {
      PlaceEventCallback(cbSizeChange, TopObject(name));
    }
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  int f[2]; int i; logic [3:0] v;\n"
      "  initial begin $arm;\n"
      "    #1 f[0] = 1; f = '{3, 4}; i = 5; v = 4'hA;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(DeliveriesOf(cbSizeChange).empty());
}

TEST_F(EventCallbacksOfARun,
       DISABLED_ASizeChangeIsReportedBeforeAnElementsValueChange) {
  Armer() = [] {
    PlaceEventCallback(cbSizeChange, TopObject("top.q"));
    vpiHandle element = vpi_handle_by_index(TopObject("top.q"), 0);
    ASSERT_NE(element, nullptr);
    EXPECT_NE(PlaceEventCallback(cbValueChange, element), nullptr);
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; int q[$] = '{1};\n"
      "  initial begin $arm; #1 q = '{5, 6}; end\n"
      "endmodule\n");
  std::vector<int> reasons;
  for (const EventDelivery& d : EventDeliveries()) reasons.push_back(d.reason);
  EXPECT_EQ(reasons, (std::vector<int>{cbSizeChange, cbValueChange}));
  EXPECT_EQ(SizesDelivered(), (std::vector<int>{2}));
  ASSERT_EQ(DeliveriesOf(cbValueChange).size(), 1U);
  EXPECT_EQ(DeliveriesOf(cbValueChange)[0].value, 5);
}

}  // namespace
}  // namespace delta
