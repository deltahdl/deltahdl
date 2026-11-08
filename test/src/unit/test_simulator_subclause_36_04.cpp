#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class SystfCallArguments : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

int g_args_seen = 0;
uint64_t g_second_arg = 0;
const char* g_user_data_seen = nullptr;
char g_user_data[] = "vector-reader";
bool g_user_data_was_read = false;

PLI_INT32 ReadArgsCalltf(PLI_BYTE8* user_data) {
  g_user_data_seen = user_data;
  g_user_data_was_read = true;
  g_args_seen = 0;
  g_second_arg = 0;
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  vpiHandle args = vpi_iterate(vpiArgument, call);
  if (args == nullptr) return 0;
  for (vpiHandle arg = vpi_scan(args); arg != nullptr; arg = vpi_scan(args)) {
    ++g_args_seen;
    if (g_args_seen == 2) {
      s_vpi_value value = {};
      value.format = vpiIntVal;
      vpi_get_value(arg, &value);
      g_second_arg = static_cast<uint64_t>(value.value.integer);
    }
  }
  return 0;
}

PLI_INT32 WriteArgCalltf(PLI_BYTE8*) {
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  vpiHandle args = vpi_iterate(vpiArgument, call);
  if (args == nullptr) return 0;
  if (vpi_scan(args) == nullptr) return 0;
  vpiHandle arg = vpi_scan(args);
  if (arg == nullptr) return 0;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 0x2D;
  vpi_put_value(arg, &value, nullptr, vpiNoDelay);
  return 0;
}

uint64_t RunGetVector(PLI_INT32 (*calltf)(PLI_BYTE8*), uint64_t bus,
                      SimFixture& f) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$get_vector");
  task.calltf = calltf;
  task.user_data = g_user_data;
  if (vpi_register_systf(&task) == nullptr) return 0;

  auto* var = RunAndFindVar(
      "module top;\n"
      "  int input_bus;\n"
      "  initial begin\n"
      "    input_bus = " +
          std::to_string(bus) +
          ";\n"
          "    $get_vector(\"test_vector.pat\", input_bus);\n"
          "  end\n"
          "endmodule\n",
      f, "input_bus");
  return var == nullptr ? 0 : var->value.ToUint64();
}

TEST_F(SystfCallArguments, BothArgumentsOfTheCallSiteAreReachable) {
  g_args_seen = 0;
  SimFixture f;
  RunGetVector(ReadArgsCalltf, 0x5A, f);

  EXPECT_EQ(g_args_seen, 2);
}

TEST_F(SystfCallArguments, AnArgumentsValueIsReadThroughTheRoutines) {
  g_second_arg = 0;
  SimFixture f;
  RunGetVector(ReadArgsCalltf, 0x5A, f);

  EXPECT_EQ(g_second_arg, 0x5Au);
}

TEST_F(SystfCallArguments, AnArgumentIsWrittenThroughTheRoutines) {
  SimFixture f;
  EXPECT_EQ(RunGetVector(WriteArgCalltf, 0x5A, f), 0x2Du);
}

TEST_F(SystfCallArguments, TheApplicationsParameterIsItsOwnUserData) {
  g_user_data_seen = nullptr;
  g_user_data_was_read = false;
  SimFixture f;
  RunGetVector(ReadArgsCalltf, 0x5A, f);

  ASSERT_TRUE(g_user_data_was_read);
  EXPECT_STREQ(g_user_data_seen, "vector-reader");
}

struct ArgumentSeen {
  int type;
  int kind;
  int value;
};
std::vector<ArgumentSeen>& KindsSeen() {
  static std::vector<ArgumentSeen> seen;
  return seen;
}

PLI_INT32 KindsCalltf(PLI_BYTE8*) {
  vpiHandle args = vpi_iterate(vpiArgument, vpi_handle(vpiSysTfCall, nullptr));
  for (vpiHandle arg = vpi_scan(args); arg != nullptr; arg = vpi_scan(args)) {
    const int kType = vpi_get(vpiType, arg);
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(arg, &value);
    KindsSeen().push_back({kType,
                           kType == vpiConstant ? vpi_get(vpiConstType, arg)
                                                : vpi_get(vpiOpType, arg),
                           value.value.integer});
  }
  return 0;
}

TEST_F(SystfCallArguments, EachArgumentKindReachesTheApplication) {
  KindsSeen().clear();
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$kinds");
  task.calltf = KindsCalltf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  SimFixture f;
  RunAndFindVar(
      "module top;\n"
      "  typedef struct packed {logic [7:0] f;} s_t;\n"
      "  s_t s = 8'h21; s_t sa [2];\n"
      "  initial begin sa[0] = 8'h43; $kinds('1, 2.5, , s.f, sa[0].f); end\n"
      "endmodule\n",
      f, "s");
  ASSERT_EQ(KindsSeen().size(), 5u);
  EXPECT_EQ(KindsSeen()[0].type, vpiConstant);
  EXPECT_EQ(KindsSeen()[0].kind, vpiIntConst);
  EXPECT_EQ(KindsSeen()[1].type, vpiConstant);
  EXPECT_EQ(KindsSeen()[1].kind, vpiRealConst);
  EXPECT_EQ(KindsSeen()[2].type, vpiOperation);
  EXPECT_EQ(KindsSeen()[2].kind, vpiNullOp);
  EXPECT_EQ(KindsSeen()[3].value, 0x21);
  EXPECT_EQ(KindsSeen()[4].value, 0x43);
}

PLI_INT32 ZeroSizetf(PLI_BYTE8*) { return 0; }

PLI_INT32 AllOnesCalltf(PLI_BYTE8*) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = -1;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

TEST_F(SystfCallArguments, ASizetfOfNoBitsLeavesTheDefaultWidth) {
  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiSizedFunc;
  func.tfname = VpiText("$zero_wide");
  func.calltf = AllOnesCalltf;
  func.sizetf = ZeroSizetf;
  ASSERT_NE(vpi_register_systf(&func), nullptr);
  SimFixture f;
  auto* r = RunAndFindVar(
      "module top; logic [63:0] r; initial r = $zero_wide(); endmodule\n", f,
      "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0xFFFFFFFFu);
}

int g_elsewhere_calls = 0;

PLI_INT32 CountCalltf(PLI_BYTE8*) {
  if (vpi_handle(vpiSysTfCall, nullptr) != nullptr) ++g_elsewhere_calls;
  return 0;
}

TEST_F(SystfCallArguments, ACallWrittenOutsideTheRunningInstanceIsReached) {
  g_elsewhere_calls = 0;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$elsewhere");
  task.calltf = CountCalltf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  SimFixture f;
  RunAndFindVar(
      "package p;\n"
      "  function automatic int f(); $elsewhere; return 1; endfunction\n"
      "endpackage\n"
      "module sub; task t(); $elsewhere; endtask endmodule\n"
      "module top; int x; sub u();\n"
      "  initial begin x = p::f(); u.t(); end\n"
      "endmodule\n",
      f, "x");
  EXPECT_EQ(g_elsewhere_calls, 2);
}

}  // namespace
}  // namespace delta
