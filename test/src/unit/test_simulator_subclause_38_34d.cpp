#include <gtest/gtest.h>

#include <functional>
#include <string>

#include "helpers_vpi_put_run.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct FunctionPutResults {
  vpiHandle saved_call = nullptr;
  int calls = 0;
  PLI_INT32 put_error = -1;
  int saved_reads = -1;
};

FunctionPutResults results;

std::function<void(vpiHandle)>& Body() {
  static std::function<void(vpiHandle)> body;
  return body;
}

std::function<void(vpiHandle)>& OtherBody() {
  static std::function<void(vpiHandle)> body;
  return body;
}

PLI_INT32 BodyCalltf(PLI_BYTE8*) {
  Body()(vpi_handle(vpiSysTfCall, nullptr));
  return 0;
}

PLI_INT32 OtherBodyCalltf(PLI_BYTE8*) {
  OtherBody()(vpi_handle(vpiSysTfCall, nullptr));
  return 0;
}

PLI_INT32 EightBits(PLI_BYTE8*) { return 8; }

int ReadSavedCall() {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(results.saved_call, &value);
  return value.value.integer;
}

void PutReturn(vpiHandle call, int value, int flags = vpiNoDelay,
               s_vpi_time* time = nullptr) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = value;
  vpi_put_value(call, &val, time, flags);
}

class SystemFunctionPutsOfARun : public VpiPutRun {
 protected:
  void SetUp() override {
    VpiPutRun::SetUp();
    results = {};
    Body() = [](vpiHandle) {};
    OtherBody() = [](vpiHandle) {};
  }

  static void Register(const char* name, PLI_INT32 type,
                       PLI_INT32 (*calltf)(PLI_BYTE8*) = &BodyCalltf,
                       PLI_INT32 (*sizetf)(PLI_BYTE8*) = nullptr) {
    s_vpi_systf_data data = {};
    data.type = vpiSysFunc;
    data.sysfunctype = type;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    data.sizetf = sizetf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static std::string BitsOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiBinStrVal;
    vpi_get_value(By(name), &value);
    return value.value.str == nullptr ? "" : value.value.str;
  }

  static void PutFiveOnTheFirstCallOnly(vpiHandle call) {
    if (results.calls++ > 0) return;
    results.saved_call = call;
    PutReturn(call, 5);
  }
};

TEST_F(SystemFunctionPutsOfARun, AnIntFunctionReturnsTheIntegerPut) {
  Register("$f", vpiIntFunc);
  Body() = [](vpiHandle call) { PutReturn(call, 42); };
  Run("module top; int r; initial r = $f; endmodule\n");
  EXPECT_EQ(IntOf("top.r"), 42);
}

TEST_F(SystemFunctionPutsOfARun,
       DISABLED_ADelayedReturnPutIsRefusedOrAppliedAtOnce) {
  Register("$f", vpiIntFunc);
  Body() = [](vpiHandle call) {
    s_vpi_time time = {vpiSimTime, 0, 3, 0.0};
    PutReturn(call, 42, vpiInertialDelay, &time);
    results.put_error = vpi_chk_error(nullptr);
  };
  Run("module top; int r, r_at5;\n"
      "  initial begin r = $f; #5 r_at5 = r; end\n"
      "endmodule\n");
  EXPECT_TRUE(results.put_error != 0 || IntOf("top.r") == 42);
  EXPECT_EQ(IntOf("top.r_at5"), IntOf("top.r"));
}

TEST_F(SystemFunctionPutsOfARun,
       DISABLED_APutToTheCallAfterItsCalltfReturnedIsIgnored) {
  Register("$f", vpiIntFunc);
  Body() = &PutFiveOnTheFirstCallOnly;
  Putter() = [] {
    PutReturn(results.saved_call, 9);
    results.saved_reads = ReadSavedCall();
  };
  Run("module top; int r, r2;\n"
      "  initial repeat (2) begin r2 = $f; if (r == 0) begin r = r2; $put; end "
      "end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.r"), 5);
  EXPECT_EQ(results.saved_reads, 5);
  EXPECT_EQ(IntOf("top.r2"), 0);
}

TEST_F(SystemFunctionPutsOfARun,
       DISABLED_APutToTheCallFromAnotherCallsCalltfIsIgnored) {
  Register("$f", vpiIntFunc);
  Register("$g", vpiIntFunc, &OtherBodyCalltf);
  Body() = &PutFiveOnTheFirstCallOnly;
  OtherBody() = [](vpiHandle call) {
    PutReturn(results.saved_call, 9);
    results.saved_reads = ReadSavedCall();
    PutReturn(call, 1);
  };
  Run("module top; int r, r2, x;\n"
      "  initial repeat (2) begin r2 = $f; if (r == 0) begin r = r2; x = $g; "
      "end end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.r"), 5);
  EXPECT_EQ(IntOf("top.x"), 1);
  EXPECT_EQ(results.saved_reads, 5);
  EXPECT_EQ(IntOf("top.r2"), 0);
}

TEST_F(SystemFunctionPutsOfARun,
       AnIntOrSizedSignedFunctionPuttingNothingIsZero) {
  Register("$i", vpiIntFunc);
  Register("$s", vpiSizedSignedFunc);
  Run("module top; int a = 5, b = 5;\n"
      "  initial begin a = $i; b = $s; end\n"
      "endmodule\n");
  EXPECT_EQ(BitsOf("top.a"), std::string(32, '0'));
  EXPECT_EQ(BitsOf("top.b"), std::string(32, '0'));
}

TEST_F(SystemFunctionPutsOfARun, ASizedFunctionPuttingNothingIsZeroOfItsWidth) {
  Register("$s8", vpiSizedFunc, &BodyCalltf, &EightBits);
  Register("$s32", vpiSizedFunc);
  Run("module top; logic [7:0] a = '1; logic [31:0] b = '1;\n"
      "  initial begin a = $s8; b = $s32; end\n"
      "endmodule\n");
  EXPECT_EQ(BitsOf("top.a"), std::string(8, '0'));
  EXPECT_EQ(BitsOf("top.b"), std::string(32, '0'));
}

TEST_F(SystemFunctionPutsOfARun, ATimeOrRealFunctionPuttingNothingIsZero) {
  Register("$t", vpiTimeFunc);
  Register("$r", vpiRealFunc);
  Run("module top; time t = 5; real r = 1.5;\n"
      "  initial begin t = $t; r = $r; end\n"
      "endmodule\n");
  EXPECT_EQ(BitsOf("top.t"), std::string(64, '0'));
  s_vpi_value real = {};
  real.format = vpiRealVal;
  vpi_get_value(By("top.r"), &real);
  EXPECT_DOUBLE_EQ(real.value.real, 0.0);
}

TEST_F(SystemFunctionPutsOfARun, ACallPuttingNothingAfterAPutOnItsLastIsZero) {
  Register("$f", vpiIntFunc);
  Body() = &PutFiveOnTheFirstCallOnly;
  Run("module top; int first, second;\n"
      "  initial repeat (2) begin second = $f; if (first == 0) first = second; "
      "end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.first"), 5);
  EXPECT_EQ(BitsOf("top.second"), std::string(32, '0'));
}

TEST_F(SystemFunctionPutsOfARun, AFunctionWithNoCalltfIsZero) {
  Register("$none", vpiIntFunc, nullptr);
  Run("module top; int a = 5; initial a = $none; endmodule\n");
  EXPECT_EQ(BitsOf("top.a"), std::string(32, '0'));
}

}  // namespace
}  // namespace delta
