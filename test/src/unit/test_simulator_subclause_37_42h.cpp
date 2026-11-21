#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_sealed_design_run.h"
#include "preprocessor/protect_processing.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct SystemCallSeen {
  std::vector<int> kinds;
  std::vector<int> op_types;
  std::vector<int> const_types;
  int reads = 0;
};

SystemCallSeen g_seen;

PLI_INT32 SeeArgumentsCalltf(PLI_BYTE8*) {
  g_seen.kinds.clear();
  g_seen.op_types.clear();
  g_seen.const_types.clear();
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  vpiHandle args = call == nullptr ? nullptr : vpi_iterate(vpiArgument, call);
  if (args == nullptr) return 0;
  while (vpiHandle arg = vpi_scan(args)) {
    const int kKind = vpi_get(vpiType, arg);
    g_seen.kinds.push_back(kKind);
    g_seen.op_types.push_back(kKind == vpiOperation ? vpi_get(vpiOpType, arg)
                                                    : 0);
    g_seen.const_types.push_back(
        kKind == vpiConstant ? vpi_get(vpiConstType, arg) : 0);
    for (int read = 0; read < g_seen.reads; ++read) {
      s_vpi_value value = {};
      value.format = vpiIntVal;
      vpi_get_value(arg, &value);
    }
  }
  return 0;
}

PLI_INT32 ReturnFortyTwoCalltf(PLI_BYTE8*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 42;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

class SystemCallsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    g_seen = SystemCallSeen();
    Register(vpiSysTask, "$see", 0, &SeeArgumentsCalltf);
    Register(vpiSysFunc, "$seef", vpiIntFunc, &SeeArgumentsCalltf);
  }

  static vpiHandle Register(int type, const char* name, int func_type,
                            PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = type;
    data.sysfunctype = func_type;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    vpiHandle registered = vpi_register_systf(&data);
    EXPECT_NE(registered, nullptr) << name;
    return registered;
  }

  static vpiHandle FirstStatement() {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    return kProcs.empty() ? nullptr : vpi_handle(vpiStmt, kProcs[0]);
  }

  static vpiHandle FirstRight() {
    vpiHandle stmt = FirstStatement();
    return stmt == nullptr ? nullptr : vpi_handle(vpiRhs, stmt);
  }

  static vpiHandle AssignedRight() {
    const std::vector<vpiHandle> kAssigns = ObjectsOf(vpiContAssign, By("top"));
    return kAssigns.empty() ? nullptr : vpi_handle(vpiRhs, kAssigns[0]);
  }

  static std::string Decompiled(vpiHandle obj) {
    const char* text =
        obj == nullptr ? nullptr : vpi_get_str(vpiDecompile, obj);
    return text == nullptr ? "" : text;
  }

  static std::vector<int> FuncTypesIn(const char* block) {
    std::vector<int> kinds;
    for (vpiHandle stmt : ObjectsOf(vpiStmt, By(block))) {
      kinds.push_back(vpi_get(vpiFuncType, vpi_handle(vpiRhs, stmt)));
    }
    return kinds;
  }
};

TEST_F(SystemCallsOfARun, AnEmptyStringArgumentIsAStringConstant) {
  Run("module top; initial $see(\"\"); endmodule\n");
  EXPECT_EQ(g_seen.kinds, std::vector<int>{vpiConstant});
  EXPECT_EQ(g_seen.const_types, std::vector<int>{vpiStringConst});
}

TEST_F(SystemCallsOfARun, ATrailingOmittedArgumentIsANullOperation) {
  Run("module top; int a; initial $see(a, ); endmodule\n");
  ASSERT_EQ(g_seen.kinds.size(), 2U);
  EXPECT_EQ(g_seen.kinds[1], vpiOperation);
  EXPECT_EQ(g_seen.op_types[1], vpiNullOp);
}

TEST_F(SystemCallsOfARun, ALeadingOmittedArgumentIsANullOperation) {
  Run("module top; int a; initial $see(, a); endmodule\n");
  ASSERT_EQ(g_seen.kinds.size(), 2U);
  EXPECT_EQ(g_seen.kinds[0], vpiOperation);
  EXPECT_EQ(g_seen.op_types[0], vpiNullOp);
}

TEST_F(SystemCallsOfARun, AFunctionCallsOmittedAndNullArgumentsKeepTheirForms) {
  Run("module top; int a, x; initial x = $seef(a, , null); endmodule\n");
  ASSERT_EQ(g_seen.kinds.size(), 3U);
  EXPECT_EQ(g_seen.kinds[1], vpiOperation);
  EXPECT_EQ(g_seen.op_types[1], vpiNullOp);
  EXPECT_EQ(g_seen.kinds[2], vpiConstant);
  EXPECT_EQ(g_seen.const_types[2], vpiNullConst);
}

TEST_F(SystemCallsOfARun, AContinuousAssignmentsSystemFunctionDecompiles) {
  Run("module top; wire [7:0] w; wire [31:0] y; assign y = $clog2(w);\n"
      "endmodule\n");
  EXPECT_EQ(Decompiled(AssignedRight()), "$clog2(w)");
}

TEST_F(SystemCallsOfARun, AProceduralSystemFunctionDecompiles) {
  Run("module top; logic [7:0] a; int x; initial x = $countones(a + 1);\n"
      "endmodule\n");
  EXPECT_EQ(Decompiled(FirstRight()), "$countones(a + 1)");
}

TEST_F(SystemCallsOfARun, AnOmittedArgumentDecompilesToAnEmptySlot) {
  Run("module top; int a, b; initial $display(a, , b); endmodule\n");
  EXPECT_EQ(Decompiled(FirstStatement()), "$display(a, , b)");
}

TEST_F(SystemCallsOfARun, ALeadingOmittedArgumentDecompilesToAnEmptySlot) {
  Run("module top; int a; initial $display(, a); endmodule\n");
  EXPECT_EQ(Decompiled(FirstStatement()), "$display(, a)");
}

TEST_F(SystemCallsOfARun, ANullArgumentDecompilesToNull) {
  Run("module top; int a; initial $display(a, null); endmodule\n");
  EXPECT_EQ(Decompiled(FirstStatement()), "$display(a, null)");
}

TEST_F(SystemCallsOfARun, ARegisteredFunctionsCallReadsAsWhatItsCalltfPut) {
  Register(vpiSysFunc, "$answer", vpiIntFunc, &ReturnFortyTwoCalltf);
  Run("module top; int z; initial z = $answer(); endmodule\n");
  vpiHandle call = FirstRight();
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(IntegerOf(call), 42);
  EXPECT_EQ(IntegerOf(By("top.z")), 42);
}

TEST_F(SystemCallsOfARun, EachFunctionCallReportsItsReturnKind) {
  Run("module top;\n"
      "  function real fr(); return 1.5; endfunction\n"
      "  function time ft(); return 2; endfunction\n"
      "  function logic signed [7:0] fs(); return -3; endfunction\n"
      "  function string fo(); return \"s\"; endfunction\n"
      "  real r; time t; logic signed [7:0] s; string o;\n"
      "  initial begin : b r = fr(); t = ft(); s = fs(); o = fo(); end\n"
      "endmodule\n");
  EXPECT_EQ(FuncTypesIn("top.b"),
            (std::vector<int>{vpiRealFunc, vpiTimeFunc, vpiSizedSignedFunc,
                              vpiOtherFunc}));
}

TEST_F(SystemCallsOfARun, DISABLED_ABuiltInSystemFunctionReportsItsReturnKind) {
  Run("module top; real r; int n; logic [7:0] a;\n"
      "  initial begin : b r = $realtime; n = $countones(a); end\n"
      "endmodule\n");
  EXPECT_EQ(FuncTypesIn("top.b"), (std::vector<int>{vpiRealFunc, vpiIntFunc}));
}

PLI_INT32 QuietCalltf(PLI_BYTE8*) { return 0; }

TEST_F(SystemCallsOfARun, EachRegisteredFunctionsCallReportsItsRegistration) {
  Register(vpiSysFunc, "$fi", vpiIntFunc, &QuietCalltf);
  Register(vpiSysFunc, "$fr", vpiRealFunc, &QuietCalltf);
  Register(vpiSysFunc, "$ft", vpiTimeFunc, &QuietCalltf);
  Register(vpiSysFunc, "$fs", vpiSizedSignedFunc, &QuietCalltf);
  Run("module top; int i; real r; time t; logic signed [31:0] s;\n"
      "  initial begin : b i = $fi(); r = $fr(); t = $ft(); s = $fs(); end\n"
      "endmodule\n");
  EXPECT_EQ(FuncTypesIn("top.b"),
            (std::vector<int>{vpiIntFunc, vpiRealFunc, vpiTimeFunc,
                              vpiSizedSignedFunc}));
}

constexpr const char* kNestedStep =
    "module top; int i = 5; int x = 1;\n"
    "  function automatic int bump(); i = i + 1; return i; endfunction\n"
    "  initial $see(x + bump());\n"
    "endmodule\n";

TEST_F(SystemCallsOfARun, ANestedOperandNoApplicationReadsIsNeverEvaluated) {
  Run(kNestedStep);
  ASSERT_EQ(g_seen.kinds.size(), 1U);
  EXPECT_EQ(IntegerOf(By("top.i")), 5);
}

TEST_F(SystemCallsOfARun, ANestedOperandIsEvaluatedEachTimeItIsRead) {
  g_seen.reads = 2;
  Run(kNestedStep);
  ASSERT_EQ(g_seen.kinds.size(), 1U);
  EXPECT_EQ(IntegerOf(By("top.i")), 7);
}

std::vector<int> g_changes;

PLI_INT32 RecordChange(p_cb_data data) {
  if (data != nullptr && data->value != nullptr) {
    g_changes.push_back(data->value->value.integer);
  }
  return 0;
}

s_vpi_time g_change_time = {vpiSimTime, 0, 0, 0.0};
s_vpi_value g_change_value = {vpiIntVal, {nullptr}};

PLI_INT32 WatchArgumentCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  vpiHandle args = call == nullptr ? nullptr : vpi_iterate(vpiArgument, call);
  vpiHandle arg = args == nullptr ? nullptr : vpi_scan(args);
  if (arg == nullptr) return 0;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = &RecordChange;
  cb.obj = arg;
  cb.time = &g_change_time;
  cb.value = &g_change_value;
  vpi_register_cb(&cb);
  return 0;
}

TEST_F(SystemCallsOfARun,
       DISABLED_AnArgumentACallbackWatchesIsEvaluatedOnChange) {
  g_changes.clear();
  Register(vpiSysTask, "$watch", 0, &WatchArgumentCalltf);
  Run("module top; int v = 1;\n"
      "  initial begin $watch(v + 10); #1 v = 9; end\n"
      "endmodule\n");
  EXPECT_EQ(g_changes, std::vector<int>{19});
}

constexpr std::string_view kKey = "call-argument-key";

class ProtectedSystemCalls : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    g_seen = SystemCallSeen();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$see");
    data.calltf = &SeeArgumentsCalltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
  SimFixture f_;
};

TEST_F(ProtectedSystemCalls, ASealedCallsArgumentsAreIterated) {
  RunUnderKey(EncryptEnvelopes("`pragma protect begin\n"
                               "module secret; int a;\n"
                               "  initial $see(a, 3);\n"
                               "endmodule\n"
                               "`pragma protect end\n"
                               "module t; secret u(); endmodule\n",
                               kKey),
              kKey, f_);
  EXPECT_EQ(g_seen.kinds.size(), 2U);
}

}  // namespace
}  // namespace delta
