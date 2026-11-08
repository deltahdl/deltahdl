#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_map>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_vpi_delays_fixture.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_put_run_delays.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

using VpiPutDelaysSim = VpiDelaysSimBase;

TEST_F(VpiPutDelaysSim, SetsDelaysInSourceOrder) {
  VpiHandle prim = MakeDelayObject(
      vpiPrimitive, {VpiDelayInfo{}, VpiDelayInfo{}, VpiDelayInfo{}});

  s_vpi_time da[3] = {};
  da[0].real = 11.0;
  da[1].real = 22.0;
  da[2].real = 33.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 3;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(prim), &delay);

  s_vpi_time out[3] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 3;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(VpiHandleOf(prim), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 11.0);
  EXPECT_DOUBLE_EQ(out[1].real, 22.0);
  EXPECT_DOUBLE_EQ(out[2].real, 33.0);
}

TEST_F(VpiPutDelaysSim, TimeTypeControlsSourceFormat) {
  VpiHandle prim =
      MakeDelayObject(vpiPrimitive, {VpiDelayInfo{}, VpiDelayInfo{}});

  s_vpi_time da[2] = {};
  da[0].low = 7u;
  da[1].low = 9u;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_put_delays(VpiHandleOf(prim), &delay);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(VpiHandleOf(prim), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 7.0);
  EXPECT_DOUBLE_EQ(out[1].real, 9.0);
}

TEST_F(VpiPutDelaysSim, DelayOnlyPutPreservesPulseLimits) {
  VpiDelayInfo seeded;
  seeded.delay = 1.0;
  seeded.reject = 40.0;
  seeded.error = 80.0;
  VpiHandle path = MakeDelayObject(vpiModPath, {seeded});

  s_vpi_time da[1] = {};
  da[0].real = 99.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 1;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(path), &delay);

  s_vpi_time out[3] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 1;
  get.time_type = vpiScaledRealTime;
  get.pulsere_flag = 1;
  vpi_get_delays(VpiHandleOf(path), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 99.0);
  EXPECT_DOUBLE_EQ(out[1].real, 40.0);
  EXPECT_DOUBLE_EQ(out[2].real, 80.0);
}

TEST_F(VpiPutDelaysSim, MtmFlagConsumesMinTypMax) {
  VpiHandle prim =
      MakeDelayObject(vpiPrimitive, {VpiDelayInfo{}, VpiDelayInfo{}});

  s_vpi_time da[6] = {};
  for (int i = 0; i < 6; ++i) da[i].real = static_cast<double>(i + 1);
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  delay.mtm_flag = 1;
  vpi_put_delays(VpiHandleOf(prim), &delay);

  s_vpi_time out[6] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  get.mtm_flag = 1;
  vpi_get_delays(VpiHandleOf(prim), &get);
  for (int i = 0; i < 6; ++i)
    EXPECT_DOUBLE_EQ(out[i].real, static_cast<double>(i + 1)) << "entry " << i;
}

TEST_F(VpiPutDelaysSim, MtmAndPulsereConsumeNineElements) {
  VpiHandle path = MakeDelayObject(vpiModPath, {VpiDelayInfo{}});

  s_vpi_time da[9] = {};
  for (int i = 0; i < 9; ++i) da[i].real = static_cast<double>(i + 1);
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 1;
  delay.time_type = vpiScaledRealTime;
  delay.mtm_flag = 1;
  delay.pulsere_flag = 1;
  vpi_put_delays(VpiHandleOf(path), &delay);

  s_vpi_time out[9] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 1;
  get.time_type = vpiScaledRealTime;
  get.mtm_flag = 1;
  get.pulsere_flag = 1;
  vpi_get_delays(VpiHandleOf(path), &get);
  for (int i = 0; i < 9; ++i)
    EXPECT_DOUBLE_EQ(out[i].real, static_cast<double>(i + 1)) << "entry " << i;
}

TEST_F(VpiPutDelaysSim, IllegalNoOfDelaysIsRejected) {
  VpiDelayInfo seeded;
  seeded.delay = 5.0;
  VpiHandle prim =
      MakeDelayObject(vpiPrimitive, {seeded, seeded, seeded, seeded});

  s_vpi_time da[4] = {};
  for (int i = 0; i < 4; ++i) da[i].real = 1000.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 4;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(prim), &delay);

  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);

  s_vpi_time out[3] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 3;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(VpiHandleOf(prim), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 5.0);
}

TEST_F(VpiPutDelaysSim, NullArgumentsAreSafe) {
  VpiDelayInfo d;
  d.delay = 1.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});

  vpi_put_delays(VpiHandleOf(prim), nullptr);

  s_vpi_delay no_array = {};
  no_array.no_of_delays = 2;
  no_array.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(prim), &no_array);

  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(nullptr, &delay);

  SUCCEED();
}

TEST_F(VpiPutDelaysSim, PulsereOnlyPutConsumesDelayRejectError) {
  VpiHandle path = MakeDelayObject(vpiModPath, {VpiDelayInfo{}});

  s_vpi_time da[3] = {};
  da[0].real = 10.0;
  da[1].real = 4.0;
  da[2].real = 8.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 1;
  delay.time_type = vpiScaledRealTime;
  delay.pulsere_flag = 1;
  vpi_put_delays(VpiHandleOf(path), &delay);

  s_vpi_time out[3] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 1;
  get.time_type = vpiScaledRealTime;
  get.pulsere_flag = 1;
  vpi_get_delays(VpiHandleOf(path), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 10.0);
  EXPECT_DOUBLE_EQ(out[1].real, 4.0);
  EXPECT_DOUBLE_EQ(out[2].real, 8.0);
}

TEST_F(VpiPutDelaysSim, TimingCheckRequiresMatchingLimitCount) {
  VpiDelayInfo a;
  a.delay = 2.0;
  VpiDelayInfo b;
  b.delay = 4.0;
  VpiHandle tchk = MakeDelayObject(vpiTchk, {a, b});

  s_vpi_time da[2] = {};
  da[0].real = 20.0;
  da[1].real = 40.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(tchk), &delay);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(VpiHandleOf(tchk), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 20.0);
  EXPECT_DOUBLE_EQ(out[1].real, 40.0);

  vpi_ctx_.ResetErrorStatus();
  s_vpi_time bad[3] = {};
  for (int i = 0; i < 3; ++i) bad[i].real = 999.0;
  s_vpi_delay bad_delay = {};
  bad_delay.da = bad;
  bad_delay.no_of_delays = 3;
  bad_delay.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(tchk), &bad_delay);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);

  vpi_ctx_.ResetErrorStatus();
  s_vpi_time after[2] = {};
  s_vpi_delay after_get = {};
  after_get.da = after;
  after_get.no_of_delays = 2;
  after_get.time_type = vpiScaledRealTime;
  vpi_get_delays(VpiHandleOf(tchk), &after_get);
  EXPECT_DOUBLE_EQ(after[0].real, 20.0);
  EXPECT_DOUBLE_EQ(after[1].real, 40.0);
}

TEST_F(VpiPutDelaysSim, IntermodulePathAcceptsTwoOrThree) {
  VpiHandle imp =
      MakeDelayObject(vpiInterModPath, {VpiDelayInfo{}, VpiDelayInfo{}});

  s_vpi_time da[2] = {};
  da[0].real = 12.0;
  da[1].real = 34.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(imp), &delay);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(VpiHandleOf(imp), &get);
  EXPECT_DOUBLE_EQ(out[0].real, 12.0);
  EXPECT_DOUBLE_EQ(out[1].real, 34.0);
}

bool g_path_written = false;
double g_rise_read_back = 0.0;
double g_fall_read_back = 0.0;

PLI_INT32 SetPathRiseFallDelaysCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;
  vpiHandle paths = vpi_iterate(vpiModPath, mod);
  if (paths == nullptr) return 0;
  vpiHandle path = vpi_scan(paths);
  if (path == nullptr) return 0;

  s_vpi_time path_da[2] = {};
  s_vpi_delay delay_s = {};
  delay_s.da = path_da;
  delay_s.no_of_delays = 2;
  delay_s.time_type = vpiScaledRealTime;
  path_da[0].real = 11.0;
  path_da[1].real = 22.0;
  vpi_put_delays(path, &delay_s);
  g_path_written = true;

  s_vpi_time read_da[2] = {};
  s_vpi_delay read_s = {};
  read_s.da = read_da;
  read_s.no_of_delays = 2;
  read_s.time_type = vpiScaledRealTime;
  vpi_get_delays(path, &read_s);
  g_rise_read_back = read_da[0].real;
  g_fall_read_back = read_da[1].real;
  return 0;
}

void RegisterPathWriteProbe() {
  g_path_written = false;
  g_rise_read_back = 0.0;
  g_fall_read_back = 0.0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &SetPathRiseFallDelaysCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

class VpiPutDelaysInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiPutDelaysInARun, TheExampleReplacesTheDelaysOfADesignsModulePath) {
  RegisterPathWriteProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output b);\n"
      "  assign b = a;\n"
      "  specify\n"
      "    (a => b) = 3;\n"
      "  endspecify\n"
      "endmodule\n"
      "module t;\n"
      "  wire p, q;\n"
      "  m m1(p, q);\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  ASSERT_TRUE(g_path_written);
  EXPECT_DOUBLE_EQ(g_rise_read_back, 11.0);
  EXPECT_DOUBLE_EQ(g_fall_read_back, 22.0);
}

TEST_F(ContAssignDelaysOfARun, PutDelaysAreTheOnesTheAssignmentTakes) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(By("top.rose"), &value);
  EXPECT_EQ(value.value.integer, 15);
  vpi_get_value(By("top.fell"), &value);
  EXPECT_EQ(value.value.integer, 26);
}

TEST_F(VpiPutDelaysSim, SuppressTimeSetsNoTimeValue) {
  VpiDelayInfo d;
  d.delay = 7.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});
  s_vpi_time da[2] = {};
  da[0].real = 3.0;
  da[1].low = 4;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiSuppressTime;
  vpi_put_delays(VpiHandleOf(prim), &delay);
  EXPECT_DOUBLE_EQ(prim->delays[0].delay, 0.0);
  EXPECT_DOUBLE_EQ(prim->delays[1].delay, 0.0);
}

TEST_F(VpiPutDelaysSim, APortIsRefusedAsItsKindSays) {
  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;

  VpiHandle interface_port = MakeDelayObject(vpiPort, {});
  interface_port->port_type = vpiInterfacePort;
  vpi_put_delays(VpiHandleOf(interface_port), &delay);
  EXPECT_STREQ(vpi_ctx_.LastError().message,
               "vpi_put_delays(): delays are not applicable to an interface "
               "port");
  EXPECT_TRUE(interface_port->delays.empty());

  VpiHandle port = MakeDelayObject(vpiPort, {});
  port->port_type = vpiPort;
  delay.no_of_delays = 1;
  vpi_put_delays(VpiHandleOf(port), &delay);
  EXPECT_STREQ(vpi_ctx_.LastError().message,
               "vpi_put_delays(): the requested number of delays is not legal "
               "for this object");
  EXPECT_TRUE(port->delays.empty());
}

TEST_F(VpiPutDelaysSim, APortWithNoLowerConnectionKeepsItsDelays) {
  VpiHandle port = MakeDelayObject(vpiPort, {});
  port->port_type = vpiPort;
  s_vpi_time da[2] = {};
  da[0].real = 4.0;
  da[1].real = 6.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(port), &delay);
  ASSERT_EQ(port->delays.size(), 2u);
  EXPECT_DOUBLE_EQ(port->delays[0].delay, 4.0);
  EXPECT_DOUBLE_EQ(port->delays[1].delay, 6.0);
}

TEST_F(VpiPutDelaysSim, AnAssignmentNoRunMadeKeepsItsDelays) {
  VpiHandle assign = MakeDelayObject(vpiContAssign, {});
  s_vpi_time da[2] = {};
  da[0].real = 2.0;
  da[1].real = 3.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(VpiHandleOf(assign), &delay);
  ASSERT_EQ(assign->delays.size(), 2u);
  EXPECT_DOUBLE_EQ(assign->delays[0].delay, 2.0);
  EXPECT_DOUBLE_EQ(assign->delays[1].delay, 3.0);
}

PLI_INT32 PutChildAssignmentDelays(PLI_BYTE8*) {
  vpiHandle it =
      vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top.u"), nullptr));
  vpiHandle ca = it != nullptr ? vpi_scan(it) : nullptr;
  if (it != nullptr) vpi_release_handle(it);
  s_vpi_time times[2] = {};
  times[0].low = 5;
  times[1].low = 6;
  s_vpi_delay delay = {};
  delay.da = times;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_put_delays(ca, &delay);
  return 0;
}

class ChildAssignmentDelaysOfARun : public VpiDesignRun {};

TEST_F(ChildAssignmentDelaysOfARun, AnInstancesAssignmentTakesThePutDelays) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$child_delays");
  data.calltf = &PutChildAssignmentDelays;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module child(input logic a); timeunit 1ns; timeprecision 1ns;\n"
      "  wire y; int rose, fell; assign y = a;\n"
      "  always @(y) if (y === 1'b1) rose = $time; else fell = $time;\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns; logic a = 0;\n"
      "  child u(.a(a));\n"
      "  initial begin #1 $child_delays; #9 a = 1; #10 a = 0; #10; end\n"
      "endmodule\n");
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(By("top.u.rose"), &value);
  EXPECT_EQ(value.value.integer, 15);
  vpi_get_value(By("top.u.fell"), &value);
  EXPECT_EQ(value.value.integer, 26);
}

vpiHandle PortNamed(const char* inst, std::string_view name) {
  vpiHandle it =
      vpi_iterate(vpiPort, vpi_handle_by_name(VpiText(inst), nullptr));
  if (it == nullptr) return nullptr;
  while (vpiHandle port = vpi_scan(it)) {
    if (name == vpi_get_str(vpiName, port)) {
      vpi_release_handle(it);
      return port;
    }
  }
  return nullptr;
}

void PutRiseOf4AndFallOf6(vpiHandle obj) {
  s_vpi_time times[2] = {};
  times[0].low = 4;
  times[1].low = 6;
  s_vpi_delay delay = {};
  delay.da = times;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_put_delays(obj, &delay);
}

PLI_INT32 PutReceiverPortDelays(PLI_BYTE8*) {
  PutRiseOf4AndFallOf6(PortNamed("top.r", "i"));
  return 0;
}

PLI_INT32 PutDriverToReceiverPathDelays(PLI_BYTE8*) {
  PutRiseOf4AndFallOf6(vpi_handle_multi(
      vpiInterModPath, PortNamed("top.d", "o"), PortNamed("top.r", "i")));
  return 0;
}

class PortDelaysOfARun : public VpiDesignRun {
 protected:
  static void RegisterTask(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static int IntOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By(name), &value);
    return value.value.integer;
  }

  static constexpr const char* kReceiver =
      "module rcv(input i); timeunit 1ns; timeprecision 1ns;\n"
      "  int rose, fell;\n"
      "  always @(i) if (i === 1'b1) rose = $time; else fell = $time;\n"
      "endmodule\n";
};

TEST_F(PortDelaysOfARun, APortTakesARiseAndFallAndReadsThemBack) {
  Run("module rcv(input i); endmodule\n"
      "module top; wire w; rcv r(w); endmodule\n");
  vpiHandle port = Named(vpiPort, By("top.r"), "i");
  ASSERT_NE(port, nullptr);
  s_vpi_time times[2] = {};
  times[0].low = 4;
  times[1].low = 6;
  s_vpi_delay delay = {};
  delay.da = times;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_put_delays(port, &delay);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiSimTime;
  vpi_get_delays(port, &get);
  EXPECT_EQ(out[0].low, 4u);
  EXPECT_EQ(out[1].low, 6u);
}

TEST_F(PortDelaysOfARun, APortsPutDelaysAreTheOnesItsConnectionTakes) {
  RegisterTask("$port_delays", &PutReceiverPortDelays);
  Run(std::string(kReceiver) +
      "module top; timeunit 1ns; timeprecision 1ns; logic a = 0; wire w;\n"
      "  assign w = a; rcv r(w);\n"
      "  initial begin #1 $port_delays; #9 a = 1; #10 a = 0; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.r.rose"), 14);
  EXPECT_EQ(IntOf("top.r.fell"), 26);
}

TEST_F(PortDelaysOfARun,
       AnIntermodulePathsPutDelaysAreTheOnesItsConnectionTakes) {
  RegisterTask("$path_delays", &PutDriverToReceiverPathDelays);
  Run(std::string(kReceiver) +
      "module drv(input a, output o); timeunit 1ns; timeprecision 1ns;\n"
      "  assign o = a;\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns; logic a = 0; wire w;\n"
      "  drv d(a, w); rcv r(w);\n"
      "  initial begin #1 $path_delays; #9 a = 1; #10 a = 0; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.r.rose"), 14);
  EXPECT_EQ(IntOf("top.r.fell"), 26);
}

TEST_F(PortDelaysOfARun, AnIntermodulePathIntoAnInoutTakesItsPutDelays) {
  RegisterTask("$path_delays", &PutDriverToReceiverPathDelays);
  Run("module rcv(inout i); timeunit 1ns; timeprecision 1ns;\n"
      "  int rose, fell;\n"
      "  always @(i) if (i === 1'b1) rose = $time; else fell = $time;\n"
      "endmodule\n"
      "module drv(input a, output o); timeunit 1ns; timeprecision 1ns;\n"
      "  assign o = a;\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns; logic a = 0; wire w;\n"
      "  drv d(a, w); rcv r(w);\n"
      "  initial begin #1 $path_delays; #9 a = 1; #10 a = 0; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.r.rose"), 14);
  EXPECT_EQ(IntOf("top.r.fell"), 26);
}

using ScaledDelaysOfAGate = VpiDesignRun;

TEST_F(ScaledDelaysOfAGate, ScaledDelaysAreInTheModulesUnit) {
  Run("module top; timeunit 1ns; timeprecision 1ps;\n"
      "  wire y; reg a;\n"
      "  buf #5 g(y, a);\n"
      "  initial $noop;\n"
      "endmodule\n");
  vpiHandle g = By("top.g");
  ASSERT_NE(g, nullptr);

  s_vpi_time read[2] = {};
  s_vpi_delay get = {};
  get.da = read;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(g, &get);
  EXPECT_DOUBLE_EQ(read[0].real, 5.0);

  s_vpi_time written[2] = {};
  written[0].real = 2.0;
  written[1].real = 2.0;
  s_vpi_delay put = {};
  put.da = written;
  put.no_of_delays = 2;
  put.time_type = vpiScaledRealTime;
  vpi_put_delays(g, &put);

  get.time_type = vpiSimTime;
  vpi_get_delays(g, &get);
  EXPECT_EQ(read[0].low, 2000u);
}

class DelaysPutInARun : public PortDelaysOfARun {
 protected:
  static void PutTwos(vpiHandle obj, int count) {
    s_vpi_time times[2] = {};
    times[0].low = 2;
    times[1].low = 2;
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = count;
    delay.time_type = vpiSimTime;
    vpi_put_delays(obj, &delay);
  }

  static PLI_INT32 PutPathDelay(PLI_BYTE8*) {
    for (vpiHandle path : ObjectsOf(vpiModPath, By("top.c"))) PutTwos(path, 1);
    return 0;
  }

  static PLI_INT32 PutPrimitiveDelays(PLI_BYTE8*) {
    PutTwos(By("top.g"), 2);
    PutTwos(By("top.u"), 2);
    return 0;
  }

  static PLI_INT32 PutCheckLimit(PLI_BYTE8*) {
    for (vpiHandle check : ObjectsOf(vpiTchk, By("top"))) PutTwos(check, 1);
    return 0;
  }
};

TEST_F(DelaysPutInARun, AModulePathTakesItsPutDelay) {
  RegisterTask("$path_put", &PutPathDelay);
  Run("module leaf(input a, output y); timeunit 1ns; timeprecision 1ns;\n"
      "  assign y = a;\n"
      "  specify (a => y) = 5; endspecify\n"
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic a = 0; wire y; int rose;\n"
      "  leaf c(a, y);\n"
      "  always @(y) if (y === 1'b1) rose = $time;\n"
      "  initial begin #1 $path_put; #9 a = 1; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.rose"), 12);
}

TEST_F(DelaysPutInARun, AGateAndAUdpTakeTheirPutDelays) {
  RegisterTask("$prim_put", &PutPrimitiveDelays);
  Run("primitive pass(output o, input i);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic a = 0; wire y, z; int gate_rose, udp_rose;\n"
      "  buf #5 g(y, a);\n"
      "  pass #5 u(z, a);\n"
      "  always @(y) if (y === 1'b1) gate_rose = $time;\n"
      "  always @(z) if (z === 1'b1) udp_rose = $time;\n"
      "  initial begin #1 $prim_put; #9 a = 1; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.gate_rose"), 12);
  EXPECT_EQ(IntOf("top.udp_rose"), 12);
}

TEST_F(DelaysPutInARun, ATimingCheckIsJudgedAgainstItsPutLimit) {
  RegisterTask("$limit_put", &PutCheckLimit);
  Run("module top(output logic d, output logic clk);\n"
      "  timeunit 1ns; timeprecision 1ns;\n"
      "  reg notifier = 0; int violations = 0;\n"
      "  specify $setup(d, posedge clk, 5, notifier); endspecify\n"
      "  always @(notifier) violations = violations + 1;\n"
      "  initial begin\n"
      "    d = 0; clk = 0;\n"
      "    #1 $limit_put;\n"
      "    #9 d = 1; #3 clk = 1; #5 clk = 0;\n"
      "    #4 d = 0; #1 clk = 1; #5;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.violations"), 1);
}

TEST(RunDelaysOfObjects, AreFiledWhereTheRunKeepsThem) {
  SimFixture f;
  SpecifyManager& specify = f.ctx.AcquireSpecifyManager();
  VpiObject net;
  net.type = vpiNet;
  net.name = "y";
  VpiObject out;
  out.type = vpiPrimTerm;
  out.direction = vpiOutput;
  out.children.push_back(&net);
  const auto kGate = [&out](const char* run_key, bool drives) {
    VpiObject gate;
    gate.type = vpiGate;
    gate.run_key = run_key;
    if (drives) gate.children.push_back(&out);
    gate.delays = {VpiDelayInfo{4.0}, VpiDelayInfo{6.0}};
    return gate;
  };
  VpiObject under_c = kGate("c.g", true);
  under_c.delays.resize(1);
  VpiObject driving_nothing = kGate("h", false);
  VpiObject holding_none = kGate("e", true);
  holding_none.delays.clear();
  VpiObject unnamed = kGate("", true);

  specify.MutableTimingChecks().resize(2);
  for (TimingCheckEntry& check : specify.MutableTimingChecks()) {
    check.limit = 5;
    check.limit2 = 5;
  }
  VpiObject two_limits;
  two_limits.type = vpiTchk;
  two_limits.delays = {VpiDelayInfo{2.0}, VpiDelayInfo{3.0}};
  VpiObject no_limits;
  no_limits.type = vpiTchk;
  const std::unordered_map<const VpiObject*, std::size_t> kEntries = {
      {&two_limits, 0}, {&no_limits, 1}};

  VpiObject* const kObjects[] = {&under_c, &driving_nothing, &holding_none,
                                 &unnamed, &two_limits,      &no_limits};
  for (VpiObject* obj : kObjects) VpiPutRunDelays(*obj, kEntries, f.ctx);
  const PrimitiveDriver* driver =
      specify.FindAnnotatedPrimitiveDriver("c.", "y");
  ASSERT_NE(driver, nullptr);
  EXPECT_EQ(driver->delays[0], 4u);
  EXPECT_EQ(driver->delays[1], 4u);
  EXPECT_EQ(driver->delays[2], 4u);
  EXPECT_EQ(specify.GetPrimitiveDrivers().size(), 1u);
  EXPECT_EQ(specify.MutableTimingChecks()[0].limit, 2u);
  EXPECT_EQ(specify.MutableTimingChecks()[0].limit2, 3u);
  EXPECT_EQ(specify.MutableTimingChecks()[1].limit, 5u);
  EXPECT_EQ(specify.MutableTimingChecks()[1].limit2, 5u);
}

}  // namespace
}  // namespace delta
