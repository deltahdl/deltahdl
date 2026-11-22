#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "helpers_run_files.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr const char* kPulseCounters =
    "  int sawx = 0, saw1 = 0, rose = 0;\n"
    "  always @(y) begin\n"
    "    if (y === 1'bx && $time > 20) sawx = sawx + 1;\n"
    "    if (y === 1'b1) begin saw1 = saw1 + 1;"
    " if (rose == 0) rose = $time; end\n"
    "  end\n";

constexpr const char* kPulses =
    "  initial begin\n"
    "    #1 $put;\n"
    "    #9 a = 1; #1 a = 0;\n"
    "    #19 a = 1; #3 a = 0;\n"
    "    #27 a = 1; #5 a = 0;\n"
    "    #20;\n"
    "  end\n";

struct ReadBack {
  uint32_t entries[6] = {};
};

ReadBack read_back;

class PutDelaysInADesign : public RunFilesRun {
 protected:
  void SetUp() override {
    RunFilesRun::SetUp();
    read_back = {};
  }

  static int IntOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By(name), &value);
    return value.value.integer;
  }

  static PLI_INT32 Put(vpiHandle obj, int count, const uint32_t* entries,
                       int pulsere) {
    s_vpi_time times[6] = {};
    for (int i = 0; i < count * (pulsere != 0 ? 3 : 1); ++i) {
      times[i].low = entries[i];
    }
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = count;
    delay.time_type = vpiSimTime;
    delay.pulsere_flag = pulsere;
    vpi_put_delays(obj, &delay);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    return kLevel;
  }

  static uint32_t FirstDelayOf(vpiHandle obj, int count) {
    s_vpi_time times[4] = {};
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = count;
    delay.time_type = vpiSimTime;
    vpi_get_delays(obj, &delay);
    return times[0].low;
  }

  static PLI_INT32 PutTwos(vpiHandle obj) {
    constexpr uint32_t kTwos[] = {2, 2};
    return Put(obj, 2, kTwos, 0);
  }

  static void ExpectPulsesFiltered() {
    EXPECT_EQ(IntOf("top.sawx"), 1);
    EXPECT_EQ(IntOf("top.saw1"), 1);
    EXPECT_EQ(IntOf("top.rose"), 70);
  }

  static std::string ModPathDesign(const char* specify_items) {
    return std::string(
               "module leaf(input a, output y); timeunit 1ns; "
               "timeprecision 1ns;\n"
               "  assign y = a;\n"
               "  specify ") +
           specify_items +
           " endspecify\n"
           "endmodule\n"
           "module top; timeunit 1ns; timeprecision 1ns;\n"
           "  logic a = 0; wire y;\n"
           "  leaf c(a, y);\n" +
           kPulseCounters + kPulses + "endmodule\n";
  }

  static PLI_INT32 PutPathPulseLimits(PLI_BYTE8*) {
    constexpr uint32_t kEntries[] = {10, 2, 4};
    for (vpiHandle path : ObjectsOf(vpiModPath, By("top.c"))) {
      Put(path, 1, kEntries, 1);
    }
    return 0;
  }

  static PLI_INT32 PutPathDelayOnly(PLI_BYTE8*) {
    constexpr uint32_t kEntries[] = {10};
    for (vpiHandle path : ObjectsOf(vpiModPath, By("top.c"))) {
      Put(path, 1, kEntries, 0);
    }
    return 0;
  }

  static vpiHandle InterModPath() {
    return vpi_handle_multi(vpiInterModPath, Named(vpiPort, By("top.d"), "o"),
                            Named(vpiPort, By("top.r"), "i"));
  }

  static PLI_INT32 PutInterModPulseLimits(PLI_BYTE8*) {
    constexpr uint32_t kEntries[] = {10, 2, 4, 10, 2, 4};
    vpiHandle path = InterModPath();
    Put(path, 2, kEntries, 1);
    s_vpi_time times[6] = {};
    s_vpi_delay delay = {};
    delay.da = times;
    delay.no_of_delays = 2;
    delay.time_type = vpiSimTime;
    delay.pulsere_flag = 1;
    vpi_get_delays(path, &delay);
    for (int i = 0; i < 6; ++i) read_back.entries[i] = times[i].low;
    return 0;
  }

  static PLI_INT32 PutSwitchDelays(PLI_BYTE8*) {
    PutTwos(By("top.s"));
    return 0;
  }

  static PLI_INT32 PutArrayElementDelays(PLI_BYTE8*) {
    PutTwos(By("top.g[0]"));
    return 0;
  }

  static PLI_INT32 PutSetupHoldLimits(PLI_BYTE8*) {
    constexpr uint32_t kLimits[] = {2, 2};
    for (vpiHandle check : ObjectsOf(vpiTchk, By("top"))) {
      Put(check, 2, kLimits, 0);
    }
    return 0;
  }
};

TEST_F(PutDelaysInADesign, DISABLED_AModulePathRunsWithThePutPulseLimits) {
  RegisterTask("$put", &PutPathPulseLimits);
  Run(ModPathDesign("(a => y) = 10;"));
  ExpectPulsesFiltered();
}

TEST_F(PutDelaysInADesign, ADelayOnlyPutKeepsTheDeclaredPulseLimits) {
  RegisterTask("$put", &PutPathDelayOnly);
  Run(ModPathDesign("specparam PATHPULSE$a$y = (2, 4); (a => y) = 7;"));
  ExpectPulsesFiltered();
}

TEST_F(PutDelaysInADesign,
       DISABLED_AnIntermodulePathRunsWithThePutPulseLimits) {
  RegisterTask("$put", &PutInterModPulseLimits);
  Run(std::string("module drv(input a, output o); timeunit 1ns;"
                  " timeprecision 1ns;\n"
                  "  assign o = a;\n"
                  "endmodule\n"
                  "module rcv(input i); timeunit 1ns; timeprecision 1ns;\n"
                  "  wire y = i;\n") +
      kPulseCounters +
      "endmodule\n"
      "module top; timeunit 1ns; timeprecision 1ns; logic a = 0; wire w;\n"
      "  drv d(a, w); rcv r(w);\n" +
      kPulses + "endmodule\n");
  constexpr uint32_t kExpected[] = {10, 2, 4, 10, 2, 4};
  for (int i = 0; i < 6; ++i) {
    EXPECT_EQ(read_back.entries[i], kExpected[i]) << "entry " << i;
  }
  EXPECT_EQ(IntOf("top.r.sawx"), 1);
  EXPECT_EQ(IntOf("top.r.saw1"), 1);
  EXPECT_EQ(IntOf("top.r.rose"), 70);
}

TEST_F(PutDelaysInADesign, APrimitiveOfARunRefusesOneOrFourDelays) {
  Run("primitive pass(output o, input i);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic a = 0, en = 1; wire y, z, w;\n"
      "  buf #5 g(y, a);\n"
      "  nmos #5 s(z, a, en);\n"
      "  pass #5 u(w, a);\n"
      "  initial $noop;\n"
      "endmodule\n");
  constexpr uint32_t kEntries[] = {9, 9, 9, 9};
  for (const char* name : {"top.g", "top.s", "top.u"}) {
    vpiHandle prim = By(name);
    ASSERT_NE(prim, nullptr) << name;
    EXPECT_EQ(Put(prim, 1, kEntries, 0), vpiError) << name;
    EXPECT_EQ(Put(prim, 4, kEntries, 0), vpiError) << name;
    EXPECT_EQ(FirstDelayOf(prim, 2), 5u) << name;
  }
}

TEST_F(PutDelaysInADesign, ATimingCheckOfARunRefusesAnotherLimitCount) {
  Run("module top(output logic d, output logic clk);\n"
      "  timeunit 1ns; timeprecision 1ns; reg notifier = 0;\n"
      "  specify $setup(d, posedge clk, 5, notifier); endspecify\n"
      "  initial $noop;\n"
      "endmodule\n");
  for (vpiHandle check : ObjectsOf(vpiTchk, By("top"))) {
    EXPECT_EQ(PutTwos(check), vpiError);
    EXPECT_EQ(FirstDelayOf(check, 1), 5u);
  }
  EXPECT_FALSE(ObjectsOf(vpiTchk, By("top")).empty());
}

TEST_F(PutDelaysInADesign, ASwitchTakesThePutDelays) {
  RegisterTask("$put", &PutSwitchDelays);
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic a = 0, en = 1; wire y; int rose;\n"
      "  nmos #5 s(y, a, en);\n"
      "  always @(y) if (y === 1'b1) rose = $time;\n"
      "  initial begin #1 $put; #9 a = 1; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.rose"), 12);
}

TEST_F(PutDelaysInADesign,
       DISABLED_AnElementOfAnInstanceArrayTakesThePutDelays) {
  RegisterTask("$put", &PutArrayElementDelays);
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  logic [1:0] a = 0; wire [1:0] y; int rose0, rose1;\n"
      "  buf #5 g[1:0](y, a);\n"
      "  always @(y[0]) if (y[0] === 1'b1) rose0 = $time;\n"
      "  always @(y[1]) if (y[1] === 1'b1) rose1 = $time;\n"
      "  initial begin #1 $put; #9 a = 2'b11; #10; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.rose0"), 12);
  EXPECT_EQ(IntOf("top.rose1"), 15);
}

TEST_F(PutDelaysInADesign, BothLimitsOfASetupHoldMoveItsWindows) {
  RegisterTask("$put", &PutSetupHoldLimits);
  Run("module top(output logic d, output logic clk);\n"
      "  timeunit 1ns; timeprecision 1ns;\n"
      "  reg notifier = 0; int violations = 0;\n"
      "  specify $setuphold(posedge clk, d, 5, 5, notifier); endspecify\n"
      "  always @(notifier) violations = violations + 1;\n"
      "  initial begin\n"
      "    d = 0; clk = 0;\n"
      "    #1 $put;\n"
      "    #9 d = 1; #3 clk = 1; #1 d = 0; #10 clk = 0;\n"
      "    #10;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.violations"), 1);
}

}  // namespace
}  // namespace delta
