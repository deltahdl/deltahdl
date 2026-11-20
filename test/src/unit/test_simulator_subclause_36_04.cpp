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

std::vector<vpiHandle> ArgumentsOfTheCall() {
  std::vector<vpiHandle> found;
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return found;
  vpiHandle args = vpi_iterate(vpiArgument, call);
  if (args == nullptr) return found;
  for (vpiHandle arg = vpi_scan(args); arg != nullptr; arg = vpi_scan(args)) {
    found.push_back(arg);
  }
  return found;
}

int IntOf(vpiHandle arg) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(arg, &value);
  return value.value.integer;
}

void ReturnInt(int result) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = result;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
}

const char* g_compiletf_user_data = nullptr;
const char* g_calltf_user_data = nullptr;

PLI_INT32 NoteCompiletfUserData(PLI_BYTE8* user_data) {
  g_compiletf_user_data = user_data;
  return 0;
}

PLI_INT32 NoteCalltfUserData(PLI_BYTE8* user_data) {
  g_calltf_user_data = user_data;
  return 0;
}

PLI_INT32 PackTheArgumentsCalltf(PLI_BYTE8*) {
  const std::vector<vpiHandle> kArgs = ArgumentsOfTheCall();
  if (kArgs.size() != 2) return 0;
  ReturnInt(IntOf(kArgs[0]) * 256 + IntOf(kArgs[1]));
  return 0;
}

PLI_INT32 WriteTheSecondArgumentCalltf(PLI_BYTE8*) {
  const std::vector<vpiHandle> kArgs = ArgumentsOfTheCall();
  if (kArgs.size() != 2) return 0;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 0x2D;
  vpi_put_value(kArgs[1], &value, nullptr, vpiNoDelay);
  ReturnInt(0x77);
  return 0;
}

void RunAFunctionCall(const std::string& body,
                      PLI_INT32 (*compiletf)(PLI_BYTE8*),
                      PLI_INT32 (*calltf)(PLI_BYTE8*), SimFixture& f) {
  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiIntFunc;
  func.tfname = VpiText("$f");
  func.compiletf = compiletf;
  func.calltf = calltf;
  func.user_data = g_user_data;
  ASSERT_NE(vpi_register_systf(&func), nullptr);
  auto* design =
      ElaborateSrc("module top;\n  int a, b, r;\n" + body + "endmodule\n", f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

uint64_t ValueOf(SimFixture& f, const char* name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

TEST_F(SystfCallArguments,
       AFunctionsRoutinesAreHandedTheUserDataNotAnArgument) {
  g_compiletf_user_data = nullptr;
  g_calltf_user_data = nullptr;
  SimFixture f;
  RunAFunctionCall("  initial begin a = 8'h5A; r = $f(a, b); end\n",
                   NoteCompiletfUserData, NoteCalltfUserData, f);
  EXPECT_STREQ(g_compiletf_user_data, "vector-reader");
  EXPECT_STREQ(g_calltf_user_data, "vector-reader");
}

TEST_F(SystfCallArguments, AFunctionsCalltfReadsTheArgumentsCurrentValues) {
  SimFixture f;
  RunAFunctionCall(
      "  initial begin\n"
      "    a = 1; b = 1;\n"
      "    #1 a = 8'h5A; b = 3;\n"
      "    r = $f(a, b);\n"
      "  end\n",
      nullptr, PackTheArgumentsCalltf, f);
  EXPECT_EQ(ValueOf(f, "r"), 0x5A03U);
}

TEST_F(SystfCallArguments, AFunctionsCalltfWritesAnArgumentAndReturnsAValue) {
  SimFixture f;
  RunAFunctionCall("  initial begin a = 8'h5A; b = 1; r = $f(a, b); end\n",
                   nullptr, WriteTheSecondArgumentCalltf, f);
  EXPECT_EQ(ValueOf(f, "b"), 0x2DU);
  EXPECT_EQ(ValueOf(f, "r"), 0x77U);
  EXPECT_EQ(ValueOf(f, "a"), 0x5AU);
}

TEST_F(SystfCallArguments, AContinuousAssignmentsCallReachesItsArguments) {
  SimFixture f;
  RunAFunctionCall(
      "  wire [31:0] w;\n"
      "  assign w = $f(a, b);\n"
      "  initial begin a = 1; b = 1; #1 a = 8'h5A; b = 3; #1 r = w; end\n",
      nullptr, PackTheArgumentsCalltf, f);
  EXPECT_EQ(ValueOf(f, "r"), 0x5A03U);
}

struct ArgumentsAtCompile {
  int count = 0;
  int last = 0;
};
ArgumentsAtCompile g_at_compile;

PLI_INT32 RecordTheArgumentsCompiletf(PLI_BYTE8*) {
  const std::vector<vpiHandle> kArgs = ArgumentsOfTheCall();
  g_at_compile.count = static_cast<int>(kArgs.size());
  if (!kArgs.empty()) g_at_compile.last = IntOf(kArgs.back());
  return 0;
}

PLI_INT32 ReturnZeroCalltf(PLI_BYTE8*) {
  ReturnInt(0);
  return 0;
}

void ExpectBothArgumentsReachTheCompiletf(const std::string& src) {
  g_at_compile = {};
  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiIntFunc;
  func.tfname = VpiText("$sf");
  func.compiletf = RecordTheArgumentsCompiletf;
  func.calltf = ReturnZeroCalltf;
  ASSERT_NE(vpi_register_systf(&func), nullptr);
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(g_at_compile.count, 2);
  EXPECT_EQ(g_at_compile.last, 7);
}

TEST_F(SystfCallArguments, DISABLED_APortConnectionsCallReachesItsArguments) {
  ExpectBothArgumentsReachTheCompiletf(
      "module sub(input logic [31:0] a); endmodule\n"
      "module top; int x; sub w (.a($sf(x, 7))); endmodule\n");
}

TEST_F(SystfCallArguments, APrimitiveTerminalsCallReachesItsArguments) {
  ExpectBothArgumentsReachTheCompiletf(
      "module top; wire z; logic b; or h (z, $sf(b, 7), b); endmodule\n");
}

TEST_F(SystfCallArguments, DISABLED_AClockingEventsCallReachesItsArguments) {
  ExpectBothArgumentsReachTheCompiletf(
      "module top; logic clk;\n"
      "  clocking cs @(posedge $sf(clk, 7)); endclocking\n"
      "endmodule\n");
}

TEST_F(SystfCallArguments, DISABLED_AConstraintsCallReachesItsArguments) {
  ExpectBothArgumentsReachTheCompiletf(
      "module top;\n"
      "  class C; rand int x; constraint c { x > $sf(1, 7); } endclass\n"
      "endmodule\n");
}

TEST_F(SystfCallArguments, DISABLED_AnExtendsClausesCallReachesItsArguments) {
  ExpectBothArgumentsReachTheCompiletf(
      "module top;\n"
      "  class B; function new(int n); endfunction endclass\n"
      "  class E extends B($sf(1, 7)); endclass\n"
      "endmodule\n");
}

void ExpectBothArgumentsReachTheCalltf(const std::string& src) {
  g_args_seen = 0;
  g_second_arg = 0;
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$get_vector");
  task.calltf = ReadArgsCalltf;
  task.user_data = g_user_data;
  ASSERT_NE(vpi_register_systf(&task), nullptr);
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(g_args_seen, 2);
  EXPECT_EQ(g_second_arg, 0x2DU);
}

TEST_F(SystfCallArguments, DISABLED_AClassMethodsTaskCallReachesItsArguments) {
  ExpectBothArgumentsReachTheCalltf(
      "module top;\n"
      "  class C;\n"
      "    task run(int v); $get_vector(\"p.pat\", v); endtask\n"
      "  endclass\n"
      "  C c;\n"
      "  initial begin c = new; c.run(45); end\n"
      "endmodule\n");
}

TEST_F(SystfCallArguments, AProgramsTaskCallReachesItsArguments) {
  ExpectBothArgumentsReachTheCalltf(
      "program top;\n"
      "  int bus;\n"
      "  initial begin bus = 45; $get_vector(\"p.pat\", bus); end\n"
      "endprogram\n");
}

TEST_F(SystfCallArguments, AnInterfacesTaskCallReachesItsArguments) {
  ExpectBothArgumentsReachTheCalltf(
      "interface ifc;\n"
      "  int bus;\n"
      "  initial begin bus = 45; $get_vector(\"p.pat\", bus); end\n"
      "endinterface\n"
      "module top; ifc u (); endmodule\n");
}

TEST_F(SystfCallArguments, AHierarchicallyCalledTasksCallReachesItsArguments) {
  ExpectBothArgumentsReachTheCalltf(
      "module sub;\n"
      "  int bus;\n"
      "  task t(); bus = 45; $get_vector(\"p.pat\", bus); endtask\n"
      "endmodule\n"
      "module top; sub u (); initial u.t(); endmodule\n");
}

}  // namespace
}  // namespace delta
