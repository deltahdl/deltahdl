#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_vpi_delays_fixture.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

using DelaysOfAnObject = VpiDelaysSimBase;

TEST_F(DelaysOfAnObject, EachKindRefusesTheCountsItDoesNotAllow) {
  const VpiDelayInfo kD;
  EXPECT_FALSE(AcceptsDelays(vpiPrimitive, 1, {kD, kD}));
  EXPECT_FALSE(AcceptsDelays(vpiPrimitive, 0, {kD, kD}));
  EXPECT_TRUE(AcceptsDelays(vpiModPath, 2, {kD, kD}));
  for (const int kCount : {0, 5, 7, 11, 13}) {
    EXPECT_FALSE(AcceptsDelays(vpiModPath, kCount, {})) << kCount;
  }
  EXPECT_FALSE(AcceptsDelays(vpiInterModPath, 1, {kD}));
}

TEST_F(DelaysOfAnObject, ASimTimeOfThirtyTwoBitsOrMoreFillsTheHighWord) {
  VpiDelayInfo d;
  d.delay = 4294967301.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});
  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_get_delays(VpiHandleOf(prim), &delay);
  EXPECT_EQ(da[0].high, 1u);
  EXPECT_EQ(da[0].low, 5u);
}

TEST_F(DelaysOfAnObject, AValidEntryTypeOtherThanTheTimeTypeIsIgnored) {
  VpiDelayInfo d;
  d.delay = 5.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});

  s_vpi_time as_real[2] = {};
  as_real[0].type = vpiSimTime;
  as_real[1].type = vpiSuppressTime;
  s_vpi_delay real_delay = {};
  real_delay.da = as_real;
  real_delay.no_of_delays = 2;
  real_delay.time_type = vpiScaledRealTime;
  vpi_get_delays(VpiHandleOf(prim), &real_delay);
  EXPECT_DOUBLE_EQ(as_real[0].real, 5.0);
  EXPECT_DOUBLE_EQ(as_real[1].real, 5.0);

  s_vpi_time as_sim[2] = {};
  as_sim[0].type = vpiScaledRealTime;
  as_sim[1].type = vpiScaledRealTime;
  s_vpi_delay sim_delay = {};
  sim_delay.da = as_sim;
  sim_delay.no_of_delays = 2;
  sim_delay.time_type = vpiSimTime;
  vpi_get_delays(VpiHandleOf(prim), &sim_delay);
  EXPECT_EQ(as_sim[0].low, 5u);
  EXPECT_EQ(as_sim[1].low, 5u);
  EXPECT_EQ(as_sim[1].high, 0u);
}

VpiDelayInfo NineFrom(double first) {
  VpiDelayInfo d;
  d.delay = first + 1;
  d.reject = first + 4;
  d.error = first + 7;
  d.min_delay = first;
  d.typ_delay = first + 1;
  d.max_delay = first + 2;
  d.min_reject = first + 3;
  d.typ_reject = first + 4;
  d.max_reject = first + 5;
  d.min_error = first + 6;
  d.typ_error = first + 7;
  d.max_error = first + 8;
  return d;
}

std::vector<double> ReadFlagged(VpiHandle obj, int mtm, int pulsere,
                                std::size_t size) {
  std::vector<s_vpi_time> da(size + 1);
  da[size].real = -7.0;
  s_vpi_delay delay = {};
  delay.da = da.data();
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  delay.mtm_flag = mtm;
  delay.pulsere_flag = pulsere;
  vpi_get_delays(VpiHandleOf(obj), &delay);
  std::vector<double> reals;
  reals.reserve(da.size());
  for (const s_vpi_time& time : da) reals.push_back(time.real);
  return reals;
}

TEST_F(DelaysOfAnObject, TheSecondDelaysRunStartsAfterTheFirstDelaysElements) {
  VpiHandle path = MakeDelayObject(vpiModPath, {NineFrom(1), NineFrom(10)});
  EXPECT_EQ(ReadFlagged(path, 0, 0, 2), (std::vector<double>{2, 11, -7}));
  EXPECT_EQ(ReadFlagged(path, 1, 0, 6),
            (std::vector<double>{1, 2, 3, 10, 11, 12, -7}));
  EXPECT_EQ(ReadFlagged(path, 0, 1, 6),
            (std::vector<double>{2, 5, 8, 11, 14, 17, -7}));
  EXPECT_EQ(ReadFlagged(path, 1, 1, 18),
            (std::vector<double>{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
                                 15, 16, 17, 18, -7}));
}

class DelaysOfARun : public VpiDesignRun {
 protected:
  static bool Refuses(vpiHandle obj, int count) {
    std::vector<s_vpi_time> da(static_cast<std::size_t>(count) + 1);
    s_vpi_delay delay = {};
    delay.da = da.data();
    delay.no_of_delays = count;
    delay.time_type = vpiSimTime;
    vpi_get_delays(obj, &delay);
    const PLI_INT32 kLevel = vpi_chk_error(nullptr);
    return kLevel == vpiError;
  }

  static std::vector<PLI_UINT32> Ticks(vpiHandle obj, int count, int mtm = 0,
                                       int pulsere = 0) {
    const int kEach = (mtm != 0 ? 3 : 1) * (pulsere != 0 ? 3 : 1);
    std::vector<s_vpi_time> da(static_cast<std::size_t>(count * kEach));
    s_vpi_delay delay = {};
    delay.da = da.data();
    delay.no_of_delays = count;
    delay.time_type = vpiSimTime;
    delay.mtm_flag = mtm;
    delay.pulsere_flag = pulsere;
    vpi_get_delays(obj, &delay);
    const PLI_INT32 kLevel = vpi_chk_error(nullptr);
    std::vector<PLI_UINT32> ticks;
    if (kLevel != 0) return ticks;
    ticks.reserve(da.size());
    for (const s_vpi_time& time : da) ticks.push_back(time.low);
    return ticks;
  }

  static void Put(vpiHandle obj, const std::vector<PLI_UINT32>& ticks,
                  int count, int mtm, int pulsere) {
    std::vector<s_vpi_time> da(ticks.size());
    for (std::size_t i = 0; i < ticks.size(); ++i) {
      da[i].type = vpiSimTime;
      da[i].low = ticks[i];
    }
    s_vpi_delay delay = {};
    delay.da = da.data();
    delay.no_of_delays = count;
    delay.time_type = vpiSimTime;
    delay.mtm_flag = mtm;
    delay.pulsere_flag = pulsere;
    vpi_put_delays(obj, &delay);
  }

  vpiHandle InterModPath() {
    Run("module drv(output o); endmodule\n"
        "module rcv(input i); endmodule\n"
        "module top; wire w;\n"
        "  drv a(.o(w)); rcv b(.i(w)); initial $noop;\n"
        "endmodule\n");
    vpiHandle out = Named(vpiPort, By("top.a"), "o");
    vpiHandle in = Named(vpiPort, By("top.b"), "i");
    if (out == nullptr || in == nullptr) return nullptr;
    return vpi_handle_multi(vpiInterModPath, out, in);
  }
};

std::vector<PLI_UINT32> OneTo(PLI_UINT32 last) {
  std::vector<PLI_UINT32> values;
  for (PLI_UINT32 v = 1; v <= last; ++v) values.push_back(v);
  return values;
}

TEST_F(DelaysOfARun, AModulePathsWrittenDelaysAreReadInWrittenOrder) {
  Run("module top(input a, output y, output z, output w);\n"
      "  timeunit 1ns; timeprecision 1ns;\n"
      "  assign y = a; assign z = a; assign w = a;\n"
      "  specify\n"
      "    (a => y) = (1, 2, 3);\n"
      "    (a => z) = (1, 2, 3, 4, 5, 6);\n"
      "    (a => w) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "  initial $noop;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kPaths = ObjectsOf(vpiModPath, By("top"));
  ASSERT_EQ(kPaths.size(), 3u);
  EXPECT_EQ(Ticks(kPaths[0], 3), OneTo(3));
  EXPECT_EQ(Ticks(kPaths[1], 6), OneTo(6));
  EXPECT_EQ(Ticks(kPaths[2], 12), OneTo(12));
}

TEST_F(DelaysOfARun, AModulePathTakesOnlyItsLegalCounts) {
  Run("module top(input a, output y); timeunit 1ns; timeprecision 1ns;\n"
      "  assign y = a;\n"
      "  specify (a => y) = (1, 2); endspecify\n"
      "  initial $noop;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kPaths = ObjectsOf(vpiModPath, By("top"));
  ASSERT_EQ(kPaths.size(), 1u);
  EXPECT_EQ(Ticks(kPaths[0], 2), (std::vector<PLI_UINT32>{1, 2}));
  for (const int kCount : {0, 5, 7, 11, 13}) {
    EXPECT_TRUE(Refuses(kPaths[0], kCount)) << kCount;
  }
}

TEST_F(DelaysOfARun, AGateSwitchAndUdpRefuseCountsOtherThanTwoOrThree) {
  Run("primitive inv_udp(o, a);\n"
      "  output o; input a;\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  wire y, z, w; logic a, c;\n"
      "  and #(3, 5) g(y, a, a);\n"
      "  nmos #(1, 2, 3) s(z, a, c);\n"
      "  inv_udp #(7, 8) u(w, a);\n"
      "  initial $noop;\n"
      "endmodule\n");
  for (const char* name : {"g", "s", "u"}) {
    vpiHandle prim = Named(vpiPrimitive, By("top"), name);
    ASSERT_NE(prim, nullptr) << name;
    EXPECT_FALSE(Refuses(prim, 2)) << name;
    for (const int kCount : {0, 1, 4}) {
      EXPECT_TRUE(Refuses(prim, kCount)) << name << " " << kCount;
    }
  }
}

TEST_F(DelaysOfARun, ASimTimeOfThirtyTwoBitsOrMoreFillsTheHighWord) {
  Run("module top; timeunit 1ns; timeprecision 1ns; wire y; logic a;\n"
      "  buf #(64'h1_0000_0005) b(y, a);\n"
      "  initial $noop;\n"
      "endmodule\n");
  vpiHandle prim = Named(vpiPrimitive, By("top"), "b");
  ASSERT_NE(prim, nullptr);
  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_get_delays(prim, &delay);
  EXPECT_EQ(da[0].high, 1u);
  EXPECT_EQ(da[0].low, 5u);
}

TEST_F(DelaysOfARun, ASuppressedTimeReadsNoValue) {
  Run("module top; timeunit 1ns; timeprecision 1ns; wire y; logic a;\n"
      "  and #(3, 5) g(y, a, a);\n"
      "  initial $noop;\n"
      "endmodule\n");
  vpiHandle prim = Named(vpiPrimitive, By("top"), "g");
  ASSERT_NE(prim, nullptr);
  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiSuppressTime;
  vpi_get_delays(prim, &delay);
  EXPECT_EQ(da[0].type, vpiSuppressTime);
  EXPECT_EQ(da[0].low, 0u);
  EXPECT_EQ(da[1].low, 0u);
  EXPECT_DOUBLE_EQ(da[0].real, 0.0);
}

TEST_F(DelaysOfARun, AModulePathsPulseLimitsFollowEachDelay) {
  Run("module top(input a, output y, output z);\n"
      "  timeunit 1ns; timeprecision 1ns;\n"
      "  assign y = a; assign z = a;\n"
      "  specify\n"
      "    specparam PATHPULSE$a$y = (2, 4);\n"
      "    (a => y) = 6;\n"
      "    (a => z) = 5;\n"
      "  endspecify\n"
      "  initial $noop;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kPaths = ObjectsOf(vpiModPath, By("top"));
  ASSERT_EQ(kPaths.size(), 2u);
  EXPECT_EQ(Ticks(kPaths[0], 1, 0, 1), (std::vector<PLI_UINT32>{6, 2, 4}));
  EXPECT_EQ(Ticks(kPaths[1], 1, 0, 1), (std::vector<PLI_UINT32>{5, 5, 5}));
}

TEST_F(DelaysOfARun, DISABLED_ATimingChecksMinTypMaxLimitIsRead) {
  Run("module m(input clk, input d); timeunit 1ns; timeprecision 1ns;\n"
      "  specify $setup(d, posedge clk, (1:2:3)); endspecify\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  reg clk, d; m m1(clk, d); initial $noop;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kChecks = ObjectsOf(vpiTchk, By("top.m1"));
  ASSERT_EQ(kChecks.size(), 1u);
  EXPECT_EQ(Ticks(kChecks[0], 1, 1), (std::vector<PLI_UINT32>{1, 2, 3}));
}

TEST_F(DelaysOfARun, AnIntermodulePathTakesThreeDelaysAndRefusesOne) {
  vpiHandle path = InterModPath();
  ASSERT_NE(path, nullptr);
  Put(path, {3, 5, 7}, 3, 0, 0);
  EXPECT_EQ(Ticks(path, 3), (std::vector<PLI_UINT32>{3, 5, 7}));
  EXPECT_TRUE(Refuses(path, 1));
}

TEST_F(DelaysOfARun, AnIntermodulePathsPulseLimitsAreRead) {
  vpiHandle path = InterModPath();
  ASSERT_NE(path, nullptr);
  const std::vector<PLI_UINT32> kLimits = {3, 1, 2, 7, 4, 5};
  Put(path, kLimits, 2, 0, 1);
  EXPECT_EQ(Ticks(path, 2, 0, 1), kLimits);
}

TEST_F(DelaysOfARun, AnIntermodulePathsMinTypMaxDelaysAreRead) {
  vpiHandle path = InterModPath();
  ASSERT_NE(path, nullptr);
  Put(path, OneTo(6), 2, 1, 0);
  EXPECT_EQ(Ticks(path, 2, 1), OneTo(6));
}

}  // namespace
}  // namespace delta
