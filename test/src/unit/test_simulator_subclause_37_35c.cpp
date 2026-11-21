#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class PrimitiveRunsOfADesign : public VpiDesignRun {
 protected:
  static void RegisterTask(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static vpiHandle Prim(const char* name) {
    return Named(vpiPrimitive, By("top"), name);
  }

  static std::vector<int> TermValuesOf(vpiHandle prim) {
    std::vector<int> values;
    for (vpiHandle term : ObjectsOf(vpiPrimTerm, prim)) {
      values.push_back(IntegerOf(term));
    }
    return values;
  }

  static std::vector<int> StrengthsOf(vpiHandle prim) {
    return {vpi_get(vpiStrength0, prim), vpi_get(vpiStrength1, prim)};
  }

  static void PutTwos(const char* name) {
    s_vpi_time times[2] = {};
    times[0].low = 2;
    times[1].low = 2;
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = 2;
    delay.time_type = vpiSimTime;
    vpi_put_delays(Prim(name), &delay);
  }

  static std::vector<int> TwoDelaysOf(const char* name) {
    s_vpi_time times[2] = {};
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = 2;
    delay.time_type = vpiSimTime;
    vpi_get_delays(Prim(name), &delay);
    return {static_cast<int>(times[0].low), static_cast<int>(times[1].low)};
  }

  static PLI_INT32 PutSwitchDelays(PLI_BYTE8*) {
    PutTwos("m");
    return 0;
  }

  static PLI_INT32 PutElementDelays(PLI_BYTE8*) {
    PutTwos("g[0]");
    return 0;
  }
};

constexpr const char* kPassUdp =
    "primitive pass_udp(o, a);\n"
    "  output o; input a;\n"
    "  table 0 : 0; 1 : 1; endtable\n"
    "endprimitive\n";

TEST_F(PrimitiveRunsOfADesign, AUdpsTermsAndValueAreThoseOfItsConnections) {
  Run("primitive mux_udp(y, s, a, b);\n"
      "  output y; input s, a, b;\n"
      "  table\n"
      "    0 0 ? : 0;\n"
      "    0 1 ? : 1;\n"
      "    1 ? 0 : 0;\n"
      "    1 ? 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top; wire y; logic s = 1, a = 0, b = 1;\n"
      "  mux_udp u(y, s, a, b);\n"
      "endmodule\n");
  EXPECT_EQ(TermValuesOf(Prim("u")), (std::vector<int>{1, 1, 0, 1}));
  EXPECT_EQ(IntegerOf(Prim("u")), 1);
}

constexpr const char* kSwitches =
    "module top; wire o, o2, v1, v2, w1, w2;\n"
    "  logic i = 0, c = 1, i2 = 1, n = 0, p = 0, en = 1;\n"
    "  assign v2 = 1'b1;\n"
    "  assign w2 = 1'b0;\n"
    "  nmos m(o, i, c);\n"
    "  cmos k(o2, i2, n, p);\n"
    "  tran t(v1, v2);\n"
    "  tranif1 t1(w1, w2, en);\n"
    "endmodule\n";

TEST_F(PrimitiveRunsOfADesign, ASwitchsTermsReadWhatTheyConnect) {
  Run(kSwitches);
  EXPECT_EQ(TermValuesOf(Prim("m")), (std::vector<int>{0, 0, 1}));
  EXPECT_EQ(TermValuesOf(Prim("k")), (std::vector<int>{1, 1, 0, 0}));
  EXPECT_EQ(TermValuesOf(Prim("t")), (std::vector<int>{1, 1}));
  EXPECT_EQ(TermValuesOf(Prim("t1")), (std::vector<int>{0, 0, 1}));
}

TEST_F(PrimitiveRunsOfADesign, ASwitchsValueIsItsOutputs) {
  Run(kSwitches);
  EXPECT_EQ(IntegerOf(Prim("m")), 0);
  EXPECT_EQ(IntegerOf(Prim("k")), 1);
}

TEST_F(PrimitiveRunsOfADesign, APutToAPrimitiveNotASequentialUdpIsRefused) {
  Run(std::string(kPassUdp) +
      "module top; wire y, o, w; wire [1:0] wa;\n"
      "  logic a = 0, i = 0, c = 1; logic [1:0] aa = 0;\n"
      "  and g(y, a, a);\n"
      "  nmos m(o, i, c);\n"
      "  pass_udp u(w, a);\n"
      "  pass_udp ua[1:0] (wa, aa);\n"
      "endmodule\n");
  const struct {
    const char* prim;
    const char* output;
  } kCases[] = {
      {"g", "top.y"}, {"m", "top.o"}, {"u", "top.w"}, {"ua[0]", "top.wa"}};
  for (const auto& c : kCases) {
    vpiHandle prim = Prim(c.prim);
    ASSERT_NE(prim, nullptr) << c.prim;
    s_vpi_value one = {};
    one.format = vpiIntVal;
    one.value.integer = 1;
    vpi_put_value(prim, &one, nullptr, vpiNoDelay);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    EXPECT_EQ(kLevel, vpiError) << c.prim;
    EXPECT_EQ(IntegerOf(By(c.output)), 0) << c.prim;
  }
}

TEST_F(PrimitiveRunsOfADesign, ASwitchTakesItsPutDelays) {
  RegisterTask("$switch_put", &PutSwitchDelays);
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic i = 0, c = 1; wire o; int rose;\n"
      "  nmos #5 m(o, i, c);\n"
      "  always @(o) if (o === 1'b1) rose = $time;\n"
      "  initial begin #1 $switch_put; #9 i = 1; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntegerOf(By("top.rose")), 12);
  EXPECT_EQ(TwoDelaysOf("m"), (std::vector<int>{2, 2}));
}

TEST_F(PrimitiveRunsOfADesign, DISABLED_AnArrayElementTakesItsPutDelays) {
  RegisterTask("$element_put", &PutElementDelays);
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic [1:0] a = 0; wire [1:0] y; int rose0, rose1;\n"
      "  buf #5 g[1:0] (y, a);\n"
      "  always @(y[0]) if (y[0] === 1'b1) rose0 = $time;\n"
      "  always @(y[1]) if (y[1] === 1'b1) rose1 = $time;\n"
      "  initial begin #1 $element_put; #9 a = 2'b11; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntegerOf(By("top.rose0")), 12);
  EXPECT_EQ(IntegerOf(By("top.rose1")), 15);
  EXPECT_EQ(TwoDelaysOf("g[0]"), (std::vector<int>{2, 2}));
  EXPECT_EQ(TwoDelaysOf("g[1]"), (std::vector<int>{5, 5}));
}

constexpr const char* kStrengths =
    "module top; wire y1, y2, y3, y4, y5, y6, p1, p2, q1, q2;\n"
    "  wire [1:0] ya; logic a, b; logic [1:0] aa;\n"
    "  and (pull0, weak1) g1(y1, a, b);\n"
    "  and (weak1, pull0) g2(y2, a, b);\n"
    "  and (highz0, strong1) g3(y3, a, b);\n"
    "  and g4(y4, a, b);\n"
    "  pass_udp (supply0, pull1) u1(y5, a);\n"
    "  pass_udp u2(y6, a);\n"
    "  and (weak0, weak1) ga[1:0] (ya, aa, aa);\n"
    "  pullup (strong1) pu1(p1);\n"
    "  pullup pu2(p2);\n"
    "  pulldown (weak0) pd1(q1);\n"
    "  pulldown pd2(q2);\n"
    "endmodule\n";

TEST_F(PrimitiveRunsOfADesign, DISABLED_AGatesWrittenStrengthsAreReported) {
  Run(std::string(kPassUdp) + kStrengths);
  const std::vector<int> kPullWeak = {vpiPullDrive, vpiWeakDrive};
  EXPECT_EQ(StrengthsOf(Prim("g1")), kPullWeak);
  EXPECT_EQ(StrengthsOf(Prim("g2")), kPullWeak);
  EXPECT_EQ(StrengthsOf(Prim("g3")),
            (std::vector<int>{vpiHiZ, vpiStrongDrive}));
}

TEST_F(PrimitiveRunsOfADesign,
       DISABLED_AGateWrittenWithNoStrengthDrivesStrong) {
  Run(std::string(kPassUdp) + kStrengths);
  EXPECT_EQ(StrengthsOf(Prim("g4")),
            (std::vector<int>{vpiStrongDrive, vpiStrongDrive}));
}

TEST_F(PrimitiveRunsOfADesign, DISABLED_AUdpInstancesStrengthsAreReported) {
  Run(std::string(kPassUdp) + kStrengths);
  EXPECT_EQ(StrengthsOf(Prim("u1")),
            (std::vector<int>{vpiSupplyDrive, vpiPullDrive}));
  EXPECT_EQ(StrengthsOf(Prim("u2")),
            (std::vector<int>{vpiStrongDrive, vpiStrongDrive}));
}

TEST_F(PrimitiveRunsOfADesign, DISABLED_AGateArraysElementsReportItsStrengths) {
  Run(std::string(kPassUdp) + kStrengths);
  for (const char* name : {"ga[0]", "ga[1]"}) {
    EXPECT_EQ(StrengthsOf(Prim(name)),
              (std::vector<int>{vpiWeakDrive, vpiWeakDrive}))
        << name;
  }
}

TEST_F(PrimitiveRunsOfADesign, DISABLED_APullSourceReportsTheStrengthItDrives) {
  Run(std::string(kPassUdp) + kStrengths);
  EXPECT_EQ(vpi_get(vpiStrength1, Prim("pu1")), vpiStrongDrive);
  EXPECT_EQ(vpi_get(vpiStrength1, Prim("pu2")), vpiPullDrive);
  EXPECT_EQ(vpi_get(vpiStrength0, Prim("pd1")), vpiWeakDrive);
  EXPECT_EQ(vpi_get(vpiStrength0, Prim("pd2")), vpiPullDrive);
}

}  // namespace
}  // namespace delta
